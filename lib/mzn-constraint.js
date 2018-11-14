const {
    Unary, Binary, Variable, Constant, GetField, PutField, DeleteField, 
    StringCharAt, StringIndexOf, StringConcat, StringSlice, StringSubstr,
    StringSplit,  NewArray, RegExpTest, RegExpExec, ToBoolean, MathAbs, 
    MathFloor, MathCeil, MathRound, MathSqrt, NumberToFixed, IsFinite
} = require("./symbolic");

const { TypeConstraint } = require("./constraint");

const Type = require("./type");

const JSPrimitive = {
    1:  "Undef",
    2:  "Null",
    4:  "Bool",
    8:  "Str",
    16: "Num",
    32: "Object"
};

const BOOL_BUILTINS = 0;
const NUM_BUILTINS  = 0;
const STR_BUILTINS  = 2;

global.N_WRITES;
global.FIRST_GET;

//TODO: Add more built-in properties. 
const BUILTIN_PROPS = new Set([
  "length", "__proto__", "constructor", 
])

const MIN_INT =  2147483647;
const MAX_INT = -2147483648;

function isIndex(n) {
    return (String(n) === "0") || (/^[1-9]\d*$/.test(n));
}

function isToType(cons) {
    switch (cons[0]) {
        case 'is-null':
            return 'TYPE_' + cons[1] + ' = Null';
        case 'is-undefined':
            return 'TYPE_' + cons[1] + ' = Undef';
        case 'is-Boolean':
            return 'TYPE_' + cons[1] + ' = Bool';
        case 'is-Num':
            return 'TYPE_' + cons[1] + ' = Num';
        case 'is-Str':
            return 'TYPE_' + cons[1] + ' = Str';
        case 'or':
            return isToType(cons[1]) + ' \\/ ' + isToType(cons[2]);
        default:
            throw new Error("Unsupported: " + cons);
    }
}

function addMiniZincConstraint(cons, model) {
    let smt_cons = "";
    try {
        smt_cons +=  "% SMT constraint: " + cons
    } 
    catch (err) {
      console.log(err)
    }
//    console.log(smt_cons)
    smt_cons += "\nconstraint ";
    if (cons instanceof Array) {
//        console.log(cons)
        model.body += smt_cons + isToType(cons) + ";\n";
        return;  
    }
    if (cons instanceof TypeConstraint) {
        preProcess(cons.subject, model);
        N_WRITES = model.N_WRITES;
        FIRST_GET = model.FIRST_GET;
        const t = toType(cons.subject);
        model.body += smt_cons + (cons.value ? t + " in " + cons.type.toJSType()
            : "not(" + t + " in " + cons.type.toJSType() + ")") + ";\n";
        return;
    }
    if (typeof(cons) === "boolean") {
        if (!cons)
            model.body += smt_cons + " false;\n";
        return;
    }
    let mzn_cons = "";
    const expr = cons.expr;
    preProcess(expr, model);
    N_WRITES = model.N_WRITES;
    FIRST_GET = model.FIRST_GET;
    if (expr instanceof Unary)
        mzn_cons += unaryRelToMZN(expr.op, expr.expr, model);    
    else if (expr instanceof Binary) {
        if (cons.value || !["<", "<=", ">=", ">"].includes(expr.op))
            mzn_cons += binaryRelToMZN(expr.op, expr.left, expr.right, model);
        else {
            model.body += smt_cons + 
               notBinaryRelToMZN(expr.op, expr.left, expr.right, model) + ";\n";
            model.FIRST_GET = FIRST_GET;
            return;
        }
    }
    else
        mzn_cons += toBool(expr);
    model.FIRST_GET = FIRST_GET;    
    model.body += smt_cons + (cons.value ? mzn_cons : not(mzn_cons)) + ";\n";
}

function preProcess(expr, model) {
    if (expr instanceof NewArray) {
        preProcess(expr.value, model)
        const v = expr.value;
        model.N_IMPL_PROPS++;
        const tv = toType(v), rv = toSval(v),
              trlv = tv + ", " + rv  + ", " + toAddr(v);
        model.body += "constraint if " + tv + " = Num then str2nat(" + rv + 
            ") != -1 /\\ set_prop_at(" + expr.id + ", \"length\", " + trlv + 
            ", " + model.N_IMPL_PROPS + ") else set_prop_at(" +  expr.id + 
            ", \"0\", " + trlv + ", " + model.N_IMPL_PROPS + ") endif;\n";
    }
    else if (expr instanceof Constant && typeof(expr.value) === "object") {
        const id = expr.objectId + 1;
        for (let key in expr.value) {
            model.N_IMPL_PROPS++;
            model.body += "constraint set_prop_at(" + id + ", \"" + key + "\", "
                + toTSA(expr.value[key]) + ", " + model.N_IMPL_PROPS + ");\n";                             
        }
    }
    else if (expr instanceof GetField) {
        if (expr.base instanceof Constant) {
            preProcess(expr.offset, model);
            // Wrappers and constant objects.
            const v = expr.base.value;
            if (typeof(v) === "object") {
                const id = expr.base.objectId + 1;
                for (let key in v) {
                    model.N_IMPL_PROPS++;
                    model.body += "constraint set_prop_at(" + id + ", \"" 
                        + key + "\", " + toTSA(expr.base.value[key]) + ", "
                        + model.N_IMPL_PROPS + ");\n";                             
                }
            }
            else
                model.N_IMPL_PROPS++;
        }
        else if (expr.base instanceof PutField) {
            preProcess(expr.base, model);
            preProcess(expr.offset, model);
        }
        else if (expr.offset instanceof Constant) {
            // Setting built-in properties, including index access.
            preProcess(expr.base, model);
            const v = expr.offset.value;
            model.N_IMPL_PROPS++;
            if ((BUILTIN_PROPS.has(v) || isIndex(v)))
                model.body += "constraint set_builtin_prop(" + 
                    toTypeSvalAddr(expr.base) + ", \"" + v + "\", " + 
                    model.N_IMPL_PROPS + ");\n";
            else {
                // Unknown base.
                const i = model.N_IMPL_PROPS;
                model.body +=
                    "constraint if is_obj(" + toType(expr.base) + ") then " + 
                    "O_ADDRS[" + i + "] = " + toAddr(expr.base) + " /\\ " + 
                    "P_NAMES[" + i + "] = \"" + v + "\" else del_prop_at(" + i 
                    + ") endif;\n";
            }
        }
        else {
            // Unknown offset, add all the builtins.
            preProcess(expr.base, model);
            preProcess(expr.offset, model);
            const offset_type = new Type(expr.offset.type);
            if (offset_type.has(Type.STRING)) {
                model.body += "constraint set_str_builtins(" 
                    + toTypeSvalAddr(expr.base) + ", " 
                    + (model.N_IMPL_PROPS + 1) + ");\n";
                model.N_IMPL_PROPS += STR_BUILTINS;
            }
            if (offset_type.has(Type.OBJECT)) {
                // Unknown base.
                model.N_IMPL_PROPS++;
                const i = model.N_IMPL_PROPS;
                model.body +=
                    "constraint if is_obj(" + toType(expr.base) + ") then " + 
                    "O_ADDRS[" + i + "] = " + toAddr(expr.base) + " /\\ " + 
                    "P_NAMES[" + i + "] = " + toSval(expr.offset) + 
                    " else del_prop_at(" + i + ") endif;\n";
            }
        }
    }
    else if (expr instanceof PutField) {
        preProcess(expr.base, model);
        preProcess(expr.offset, model);
        preProcess(expr.val, model);
        model.N_EXPL_PROPS++;
        model.N_WRITES++;
        model.body += "constraint put_prop(" + toTypeAddr(expr.base) + ", " + 
            toSval(expr.offset) + ", " + toTypeSvalAddr(expr.val) + 
                ", N_IMPL_PROPS + " + model.N_WRITES + ");\n";
    }
    else if (expr instanceof DeleteField) {
        preProcess(expr.base, model);
        preProcess(expr.offset, model);
        model.N_EXPL_PROPS++;
        model.N_WRITES++;
        model.body += "constraint del_prop(" + toTypeAddr(expr.base) + ", " + 
            toSval(expr.offset) + ", N_IMPL_PROPS + " + model.N_WRITES + ");\n";
    }
    else if (expr instanceof Unary) {
        if  (expr.expr instanceof PutField)
            preProcess(expr.expr.base, model);
        else
            preProcess(expr.expr, model);
    }
    else if (expr instanceof Binary) {
        if  (expr.left instanceof PutField && expr.left.base instanceof Variable)    
            preProcess(expr.left.base, model);
        else
            preProcess(expr.left, model);
        if  (expr.right instanceof PutField && expr.right.base instanceof Variable)    
            preProcess(expr.right.base, model);
        else
            preProcess(expr.right, model);
    }
    else if (expr instanceof ToBoolean) {
        preProcess(expr.value, model);
    }
    else if (expr instanceof StringIndexOf) {
        preProcess(expr.searchString, model);
        preProcess(expr.base, model);
        preProcess(expr.offset, model);
        preProcess(expr.start, model);
    }
    else if (expr instanceof StringCharAt) {
        preProcess(expr.idx, model);
        preProcess(expr.base, model);
    }
    else if (expr instanceof StringConcat) {
        preProcess(expr.base, model);
        preProcess(expr.args, model);
    }
    else if (expr instanceof StringSlice) {
        preProcess(expr.base, model);
        preProcess(expr.start, model);
        preProcess(expr.end, model);
    }
    else if (expr instanceof StringSplit) {
        preProcess(expr.base, model);
        preProcess(expr.sep, model);
    }
    else if (expr instanceof StringSubstr) {
        preProcess(expr.base, model);
        preProcess(expr.start, model);
        preProcess(expr.len, model);
    }
    else if (expr instanceof RegExpTest) {
        preProcess(expr.str, model);
    }
    else if (expr instanceof MathAbs || expr instanceof MathCeil || 
           expr instanceof MathFloor || expr instanceof MathSqrt)
        preProcess(expr.num, model);
    else if (expr instanceof NumberToFixed) {
        preProcess(expr.base, model);
        preProcess(expr.fracDigits, model);
    }
    else if (expr instanceof IsFinite)
        preProcess(expr.val, model);
}

function mznLiteral(x) {
    let s = "";
    let ascii = true;
    for (let i = 0; i < x.length; ++i) {
        const ch = x.charCodeAt(i);
        if (ch < 32 || ch > 256)
            ascii = false;
        s += ("\\\\x" + ch.toString(16)).slice(-4);
    }
    if (ascii)
        return "\"" + x + "\"";
    else
        return "\"" + s + "\"";
}

function escapeRegExp(x) {
    return x.replace(/\\/g, "\\\\\\").replace(/\./g, "\\\\.").
        replace(/\(/g, "\\\\(").replace(/\)/g, "\\\\)").replace(/\*/g, "\\\\*").
        replace(/\[/g, "\\\\[").replace(/\]/g, "\\\\]").replace(/\|/g, "\\\\|");
}

function mznRegExpBound(re) {
    let x = re.substr(1, re.length - 2);
    const c = x.charCodeAt(0);
    if (x.length > 1)
        x = "\\" + x
    return x;
}

function mznRegExp(re) {
  switch (re) {
     case "re.allchar":
          return "(.*)"; 
  }
  switch (re[0]) {
      case "str.to.re":
          return  escapeRegExp(re[1].substr(1, re[1].length - 2));
      case "re.*":
          return "(" + mznRegExp(re[1]) + ")*";
      case "re.+":
          const r = mznRegExp(re[1]);
          return "(" + r + r + "*)";          
      case "re.opt":
          return "(()|" + mznRegExp(re[1]) + ")";
      case "re.++":
          let rc = "(";
          for (let i = 1; i < re.length; ++i)
              rc += mznRegExp(re[i]);
          return rc + ")";
      case "re.union":
          let ru = "(";
          const n = re.length - 1;
          for (let i = 1; i < n; ++i)
              ru += mznRegExp(re[i]) + "|"
          return ru + mznRegExp(re[n]) + ")";
      case "re.range":
          return "[" + mznRegExpBound(re[1]) + "-" + mznRegExpBound(re[2]) + "]"
      case "re.loop":
          const l = re[2], u = re[3];
          if (re[1][0] === "re.range") {
            const a = mznRegExpBound(re[1][1]), b = mznRegExpBound(re[1][2]);                  
            if (typeof(u) === "number")
                return "[" + a + "-" + b + "," + l + "," + u + "]";
            else
                return "[" + a + "-" + b + "," + l + "]";
          }
          let r1 = mznRegExp(re[1]), r2 = "(" + r1.repeat(l) + ")";
          if (typeof(u) === "number")
              r2 += "(" + ("(" + r1 + "|())").repeat(u) + ")";
          else
              r2 += "(" + r1 + ")*";
          return r2;
      case "re.inter":
          let ri = "(";
          const m = re.length - 1;
          for (let i = 1; i < m; ++i)
              ri += mznRegExp(re[i]) + "&"
          return ri + mznRegExp(re[m]) + ")";
      default:
          throw new Error("Unsupported regex! " + re)
  }
}

function fromTSA(expr, suff) {
    if (expr instanceof Constant) {
        if (suff == "TYPE")
            return expr.value === null ? "Null" : JSPrimitive[expr.getType()]
        else if (suff == "SVAL") {
            if (typeof expr.value === "string")
                return mznLiteral(expr.value)
            else
                return "\"" + expr.value + "\""
        }
        else
            return typeof(expr.value) === "object" && expr.value !== null ? 
              expr.objectId + 1 : "0";
    }
    else if (expr instanceof Variable) {
        if (suff === "ADDR")
           return "ADDR_" + expr.name
        else  
           return suff + "_" + expr.name
    }
    else if (expr instanceof GetField) {
        if (expr.base instanceof Constant) {
            // Wrappers and constant objects.
            const v = expr.base.value;
            switch (typeof(v)) {
                case "string":
                    return "P_" + suff + "S[get_str_prop(\"" + v + "\", " + 
                        toSval(expr.offset) + ", )]";
                case "number":
                    return "P_" + suff + "S[get_num_prop(\"" + v + "\", " + 
                        toSval(expr.offset) + ", )]";
                case "boolean":
                    return "P_" + suff + "S[get_bool_prop(\"" + v + "\", " +
                        toSval(expr.offset) + ", )]";
//                case "function":
                default:
                    const val = "P_" + suff + "S[get_prop(Object, " + 
                        (expr.base.objectId + 1) + ", " + toSval(expr.offset) + 
                        ", N_IMPL_PROPS)]";
//                    TODO:
//                    if (v instanceof Array) {
//                        if (suff === "TYPE")
//                            return "if " + toSval(expr.offset) + ' = "length" then Num else ' + val;
//                        else if (suff === "SVAL")
//                            return "if " + toSval(expr.offset) + ' = "length" then array_length(' + 
//                                toAddr(expr.offset) + ', N_IMPL_PROPS) else ' + val;
//                        else
//                            return "if " + toSval(expr.offset) + ' = "length" then 0 else ' + val;
//                    }
                    //FIXME: builtin objects, e.g. Math?
                    return val;
            }
        }
        else {
            if (FIRST_GET[expr.base] === undefined)
                FIRST_GET[expr.base] = N_WRITES;
            const val = "P_" + suff + "S[get_prop(" + toTypeAddr(expr.base) + 
                ", " + toSval(expr.offset) + ", N_IMPL_PROPS + " + N_WRITES + ")]";
//            TODO:
//            if (expr.offset.value === "length") {
//                if (suff === "TYPE")
//                    return "if " + toType(expr.base) + ' = Array then Num else ' + val;
//                else if (suff === "SVAL")
//                    return "if " + toType(expr.base) + ' = Array then array_length(' + 
//                        toAddr(expr.offset) + ', N_IMPL_PROPS + N_WRITES) else ' + val;
//                else
//                    return "if " + toType(expr.base) + ' = Array then 0 else ' + val;
//            }
//            else
                return val;
        }
    }
    else if (expr instanceof PutField)
        return fromTSA(expr.base, suff)
    else if (expr instanceof DeleteField)
        return fromTSA(expr.base, suff)
    else if (expr instanceof Unary)
        return unaryOpToMZN(expr.op, expr.expr, suff);
    else if (expr instanceof Binary)
        return binaryOpToMZN(expr.op, expr.left, expr.right, suff);
    else if (expr instanceof NewArray) {
        if (suff === "TYPE")
            return "Array";
        else if (suff === "SVAL")
            return ""; //FIXME: Array representation to be done!;
        else
            return expr.id;
    }
    else if (expr instanceof ToBoolean) {
        if (suff === "TYPE")
            return "Bool";
        else if (suff === "SVAL")
            return toBool(expr.value);
        else
            return "0";           
    }
    else if (expr instanceof StringIndexOf) {
        if (suff === "TYPE")
            return "Num";
        else if (suff === "SVAL") {
            const x = toSval(expr.searchString);
            const y = toSval(expr.base);
            const i = toNum(expr.offset);
            if (i === "\"0\"")
                return "int2str(str_find(" + x + ", " + y + ") - 1)";
            else {
                const i = toNum(expr.start);
                const j = isNaN(Number(i0)) ? 
                    "str2nat(" + i + ")" : i.slice(1, i.length - 1);
                return "int2str(str_find(" + x + ", str_sub(" + y + ", " + j + 
                    ", str_len(" + y + "))) + " + j + " - 1)";
            }
        }
        else
            return "0";
    }
    else if (expr instanceof StringCharAt) {
        if (suff === "TYPE")
            return "Str"
        else if (suff === "SVAL") {
            const i = toNum(expr.idx);
            const j = isNaN(Number(expr.idx)) ? 
                "str2nat(" + i + ")" : i.slice(1, i.length - 1);
            return "str_char_at(" + toSval(expr.base) + ", " + j + " + 1)";
        }
        else
            return "0"
    }
    else if (expr instanceof StringConcat) {
        if (suff === "TYPE")
            return "Str"
        else if (suff === "SVAL") {          
            const args = expr.args, n = args.length - 1;
            let c = toSval(expr.base) + " ++ ";
            for (let i = 0; i < n; ++i)
                c += toSval(args[i]) + " ++ ";
            return c + toSval(args[n]);
        }
        else
            return "0"
    }
    else if (expr instanceof StringSlice) {
        if (suff === "TYPE")
            return "Str"
        else if (suff === "SVAL") {          
            const i0 = toNum(expr.start);
            const j0 = isNaN(Number(i0)) ? 
                "str2nat(" + i0 + ")" : i0.slice(1, i0.length - 1);
            const i1 = toNum(expr.end);
            const j1 = isNaN(Number(i1)) ?
                "str2nat(" + i1 + ")" : i1.slice(1, i1.length - 1);
            return "str_sub(" + toSval(expr.base) + ", " + j0 + " + 1, " + j1 + ")";
        }
        else
            return "0"
    }
    else if (expr instanceof StringSplit) {
       if (suff === "TYPE")
           return "Array";
       let l;
       // FIXME: Workaround! MiniZinc does not handle dynamic arrays.
       if (!expr.base instanceof Constant || expr.base.value === undefined)
           l = 10;
       else
           l = toNum(expr.len);
       if (suff === "SVAL")
           // TODO: 
           return "split_REP(" + toSval(expr.base) + ", " + toSval(expr.sep) 
               + ", " + l + ")";
       else
           // TODO:
           return "split_LOC(" + toSval(expr.base) + ", " + toSval(expr.sep) 
               + ", " + l + ")";
    }
    else if (expr instanceof StringSubstr) {
        if (suff === "TYPE")
            return "Str"
        else if (suff === "SVAL") {          
            const i0 = toNum(expr.start);
            const j0 = isNaN(Number(i0)) ? 
                "str2nat(" + i0 + ")" : i0.slice(1, i0.length - 1);
            const i1 = toNum(expr.len);
            const j1 = isNaN(Number(i1)) ?
                "str2nat(" + i1 + ")" : i1.slice(1, i1.length - 1);
            //FIXME: Not taking into account negative length atm.
            return "str_sub(" + toSval(expr.base) + ", " + j0 + " + 1, " + 
                j0 + " + " + j1 + ")";
        }
        else
            return "0"
    }    
    else if (expr instanceof RegExpTest) {
        if (suff === "TYPE")
            return "Bool";
        else if (suff === "SVAL")        
            return "str_reg(" + toSval(expr.str) + ", \"" + 
                mznRegExp(expr.toBooleanFormula()[2]) + "\")";
        else
            return "0";
    }
    else if (expr instanceof RegExpExec) {
        console.log("FIXME: Ignoring " + expr);
        if (suff === "TYPE")
            return "Array";
        else if (suff === "SVAL")        
            return "\"\""; //FIXME: TBD
        else
            return String(_resultObjId);        
    }
    else if (expr instanceof MathAbs) {
        if (suff === "TYPE")
            return "Num";
        else if (suff === "SVAL")
            return "absv(" + toNum(expr.num) + ")";
        else
            return "0";
    }
    else if (expr instanceof MathFloor) {
        if (suff === "TYPE")
            return "Num";
        else if (suff === "SVAL")
            return "floor(" + toNum(expr.num) + ")";
        else
            return "0";
    }
    else if (expr instanceof MathCeil) {
        if (suff === "TYPE")
            return "Num";
        else if (suff === "SVAL")
            return "ceil(" + toNum(expr.num) + ")";
        else
            return "0";
    }
    else if (expr instanceof MathRound) {
        if (suff === "TYPE")
            return "Num";
        else if (suff === "SVAL")
            return "round(" + toNum(expr.num) + ")";
        else
            return "0";
    }
    else if (expr instanceof MathSqrt) {
        if (suff === "TYPE")
            return "Num";
        else if (suff === "SVAL")
            return "sqrt(" + toNum(expr.num) + ")";
        else
            return "0";
    }
    else if (expr instanceof NumberToFixed) {
        if (suff === "TYPE")
            return "Str";
        else if (suff === "SVAL")
            return "to_fixed(" + toSval(expr.base) + ", " + 
                toNum(expr.fracDigits) + ")";
        else
            return "0";
    }
    else if (expr instanceof IsFinite) {
        if (suff === "TYPE")
            return "Bool";
        else if (suff === "SVAL")
            return "is_finite(" + toNum(expr.val) + ")";
        else
            return "0";
    }
    else {
        console.log(expr)
        throw new Error("Unsupported: " + expr);
    }
}

function toTSA(x) {
  switch (typeof(x)) {
      case "null":
          return "Null, \"null\", 0";
      case "undefined":
          return "Undef, \"undefined\", 0";
      case "boolean":
          return "Bool, \"" + x + "\", 0";
      case "number":
          return "Num, \"" + x + "\", 0";
      case "string":
          return "Str, \"" + x + "\", 0";
      default:
          throw new Error("Unsupported: " + x);
  }
}

function toType(x) {
    return fromTSA(x, "TYPE");
}
function toSval(x) {
    return fromTSA(x, "SVAL");
}
function toAddr(x) {
    return fromTSA(x, "ADDR");
}
function toTypes(x, y) {
    return toType(x)  + ", "  + toType(y)
}
function toTypeSval(x) {
    return toType(x)  + ", "  + toSval(x)
}
function toTypeAddr(x) {
    return toType(x)  + ", "  + toAddr(x)
}
function toTypeSvals(x, y) {
    return toTypeSval(x) + ", "  + toTypeSval(y)
}
function toTypeSvalAddr(x) {
    return toType(x)  + ", "  + toSval(x)  + ", " + toAddr(x);
}
function toTypeSvalAddrs(x, y) {
    return toTypeSvalAddr(x)  + ", "  + toTypeSvalAddr(y);
}

function toBool(x) {
    const tx = toType(x);
    const rx = toSval(x);
    return tx === "Bool" ? rx : "to_bool_var(" + tx + ", " + rx + ")";
}
function toNum(x) {
    const tx = toType(x);
    const rx = toSval(x);
    if (+rx < MIN_INT || +rx > MAX_INT)
        console.log("Warning! Integer overflow detected (" + rx + ").")
    return tx === "Num" ? rx : "to_num(" + tx + ", " + rx + ")";
}
function toNum0(x) {
    const tx = toType(x);
    const rx = toSval(x);
    return tx === "Num" ? rx : "to_num_0(" + tx + ", " + rx + ")";
}
 
function negate(x) {
  return x.startsWith("negate(") ? x.slice(7, x.length-1) : "negate(" + x + ")";
}

function not(x) {
  return x.startsWith("not(") ? x.slice(4, x.length - 1) : "not(" + x + ")";
}

///// Unary /////

function unaryRelToMZN(op, arg) {
    switch (op) {
        case "!":
            if (arg instanceof Unary)
                return not(unaryRelToMZN(arg.op, arg.expr));
            else if (arg instanceof Binary)
                return notBinaryRelToMZN(arg.op, arg.left, arg.right);
            else
                return not(toBool(arg));
        default:
            return "to_bool_var(" + unaryOpToMZN(op, arg, "TYPE") + ", " 
                                  + unaryOpToMZN(op, arg, "SVAL") + ")";
    }
}

function unaryOpToMZN(op, arg, suff) {
    switch (suff) { 
        case "TYPE": {
            switch (op) {
                case "typeof":
                    return "Str";
                case "+":
                case "-":
                    return "Num";
                case "!":
                    return "Bool";
            }
        }    
        case "SVAL": {
            switch (op) {
                case "typeof":
                    return "typeof(" + toType(arg) + ")";
                case "+":
                    return toNum(arg);
                case "-":
                    return negate(toNum(arg));
                case "!":
                    return toBool(arg);
            }
        }
        case "ADDR": {
            switch (op) {
                case "typeof":
                case "+":
                case "-":
                case "!":
                    return "0";
            }
        }
    }
    throw new Error("Unsupported unary: " + op);
}

///// Binary /////

function arithBop(op, x, y) {
    switch (op) {
        case "+":
            return "plus_REP(" + toTypeSvals(x, y) + ")";
        case "-":
            return "sub(" + toNum(x) + ", " + toNum(y) + ")";
        case "*":
            return "mul(" + toNum(x) + ", " + toNum(y) + ")";
        case "/":
            return "divs(" + toNum(x) + ", " + toNum0(y) + ")";
        case "%":
            return "mods(" + toNum(x) + ", " + toNum(y) + ")";
    }
}

function binaryOpToMZN(op, left, right, suff) {
    switch (suff) {
        case "TYPE": {
            switch (op) {
                case "+":
                    const lhs = toType(left);
                    const rhs = toType(right);
                    if (['Null', 'Bool', 'Num'].includes(lhs) && 
                        ['Null', 'Bool', 'Num'].includes(rhs))
                        return "Num";
                    else if (lhs === "Str" || rhs === "Str")
                        return "Str";
                    else
                        return "plus_TYP(" + toTypes(left, right) + ")";
                case "-":
                case "*":
                case "/":
                case "%":
                    return "Num";
            }
        }
        case "SVAL": {
            switch (op) {
                case "+":
                case "-":
                case "*":
                case "/":
                case "%":
                    return arithBop(op, left, right);
            }
        }
        case "ADDR": {
            switch (op) {
                case "+":
                case "-":
                case "*":
                case "/":
                case "%":
                    return "0"
            }
        }
    }
    throw new Error("Unsupported binary: " + op);
}

function notBinaryRelToMZN(op, left, right) {
    switch (op) {
        case "<":
            return "not_lt(" + toTypeSvals(left, right) + ")";
        case "<=":
            return "not_le(" + toTypeSvals(left, right) + ")";
        case ">":
            return "not_lt(" + toTypeSvals(right, left) + ")";
        case ">=":
            return "not_le(" + toTypeSvals(right, left) + ")";
        default:
            return not(binaryRelToMZN(op, left, right));
    };
}

function binaryRelToMZN(op, left, right) {
    switch (op) {
        case "<":
            return "lt(" + toTypeSvals(left, right) + ")";
        case "<=":
            return "le(" + toTypeSvals(left, right) + ")";
        case ">":
            return "lt(" + toTypeSvals(right, left) + ")";
        case ">=":
            return "le(" + toTypeSvals(right, left) + ")";
        case "==":
            return "abstract_eq(" + toTypeSvalAddrs(left, right) + ")";
        case "===":
            return "strict_eq(" + toTypeSvalAddrs(left, right) + ")";
        case "!=":
            return "not(abstract_eq(" + toTypeSvalAddrs(left, right) + "))";
        case "!==":
            return "not(strict_eq(" + toTypeSvalAddrs(left, right) + "))";
        case "in":
            return "is_def("+ toSval(left) + ", " + toTypeAddr(right) +")";
        default:
            return "to_bool_var(" + binaryOpToMZN(op, left, right, "TYPE") + ", " 
                                  + binaryOpToMZN(op, left, right, "SVAL") + ")";
    }
}

exports.addMiniZincConstraint = addMiniZincConstraint; 
