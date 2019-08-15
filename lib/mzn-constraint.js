const {
    Unary, Binary, Variable, Constant, GetField, PutField, DeleteField, 
    StringCharAt, StringIndexOf, StringConcat, StringSlice, StringSubstr,
    StringSplit,  NewArray, RegExpTest, RegExpExec, ToBoolean, ToString, MathAbs, 
    MathFloor, MathCeil, MathRound, MathSqrt, NumberToFixed, NumberIsFinite,
    NumberIsNaN, IsFinite, IsNaN, StringToString, StringToLowerCase, Temporary,
    StringToUpperCase, ToObject, StringRepeat, StringIncludes, ArrayIncludes,
    StringCharCodeAt
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

const BOOL_BUILTINS  = 0;
const NUM_BUILTINS   = 0;
const STR_BUILTINS   = 2;
const ARRAY_BUILTINS = 2;

global.N_WRITES;
global.FIRST_GET;
global.TMP_ADDR;

//TODO: Add more built-in properties. 
const BUILTIN_PROPS = new Set([
  "length", "__proto__", "constructor", 
])

const MIN_INT = -2147483648;
const MAX_INT =  2147483647;

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
        case 'is-Obj':
            return 'TYPE_' + cons[1] + ' = Object';
        case 'or':
            return isToType(cons[1]) + ' \\/ ' + isToType(cons[2]);
        default:
            throw new Error("Unsupported: " + cons);
    }
}

function addMiniZincConstraint(cons, model) {
    let smt_cons =  '' + cons
//    console.log(smt_cons)
    if (smt_cons === "true")
        return;
    if (smt_cons === "false") {
        model.body += "constraint false; %FIXME: =====UNSATISFIABLE=====\n";
        return;
    }
    if (model.SMT_CONS.has(smt_cons))
        return;
    else
        model.SMT_CONS.add(smt_cons)
    try {
        smt_cons = "% SMT constraint: " + smt_cons
    } 
    catch (err) {
      console.log(err)
      smt_cons = ''
    }    
//    console.log(smt_cons)
    smt_cons += "\nconstraint ";
    if (cons instanceof Array) {
//        console.log(cons)
        model.body += smt_cons + isToType(cons) + ";\n";
        return;
    }
    TMP_ADDR = {}
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
            model.body += smt_cons + " false; %FIXME: =====UNSATISFIABLE=====\n";
        return;
    }
    let mzn_cons = "";
    const expr = cons.expr;
    preProcess(expr, model);
    N_WRITES = model.N_WRITES;
    FIRST_GET = model.FIRST_GET;
    if (expr instanceof Unary)
        mzn_cons += unaryRelToMZN(expr.op, expr.expr);    
    else if (expr instanceof Binary) {
        if (cons.value || !["<", "<=", ">=", ">"].includes(expr.op))
            mzn_cons += binaryRelToMZN(expr.op, expr.left, expr.right);
        else {
            model.body += smt_cons + 
               notBinaryRelToMZN(expr.op, expr.left, expr.right) + ";\n";
            model.FIRST_GET = FIRST_GET;
            return;
        }
    }
    else
        mzn_cons += toBool(expr);
    model.FIRST_GET = FIRST_GET;    
    model.body += smt_cons + (cons.value ? mzn_cons : not(mzn_cons)) + ";\n";
}

function add_tmp_addr(expr, model) {
    model.N_ADDRS++;
    const id = model.N_ADDRS, v = "TMP_ADDR_" + id;
    model.body += "int: " + v + " = " + id + ";\n"
    TMP_ADDR[toSval(expr)] = v;
    model.TMP_ADDRS.push(id);
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
        model.N_ADDRS++;
        const id = expr.objectId + 1;
        for (let key in expr.value) {
            model.N_ADDRS++;
            model.N_IMPL_PROPS++;
            model.body += "constraint set_prop_at(" + id + ", \"" + key + "\", "
                + toTSA(expr.value[key]) + ", " + model.N_IMPL_PROPS + ");\n";                             
        }
    }
    else if (expr instanceof GetField) {
        if (expr.base instanceof Constant) {
            model.N_ADDRS++;
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
        else if (expr.base instanceof PutField 
              || expr.base instanceof DeleteField) {
            preProcess(expr.base, model);
            preProcess(expr.offset, model);
        }
        else if (expr.base instanceof RegExpExec) {
            model.N_IMPL_PROPS++;
            preProcess(expr.base, model);
            preProcess(expr.offset, model);
            model.body += "constraint set_prop_at(" + expr.base._resultObjId + 
                ", \"" + expr.offset.value + "\", Str, " + 
                (expr.offset.value
                     ? toSval(expr.base._caps[expr.offset.value - 1])
                     : toSval(expr.base._temps[0]))
                + ", 0, " + model.N_IMPL_PROPS + ");\n";
        }
        else if (expr.offset instanceof Constant) {
            // Setting built-in properties, including index access.
            preProcess(expr.base, model);
            const v = expr.offset.value;            
            if ((BUILTIN_PROPS.has(v) || (isIndex(v)))) {
                model.N_IMPL_PROPS++;
                const sval = toSval(expr.base);
                const id = TMP_ADDR[sval];
                if (id === undefined)
                    model.body += "constraint set_builtin_prop(" 
                    + toType(expr.base) + ", " + sval + ", " + toAddr(expr.base) 
                    + ", " + mznLiteral(v) + ", " + model.N_IMPL_PROPS + ");\n";
                else
                    model.body += "constraint set_builtin_prop(" 
                    + toType(expr.base) + ", " + sval + ", " + id 
                    + ", " + mznLiteral(v) + ", " + model.N_IMPL_PROPS + ");\n";
                model.MAYBE_ARRAY = true;
            }
            // Base is unknown.
            const t = toType(expr.base);
            if (!["Null", "Undef", "Bool", "Num", "Str", "Array"].includes(t)) {
                model.N_IMPL_PROPS++;
                const i = model.N_IMPL_PROPS;
                model.body +=
                    "constraint if " + t + " = Object then " + 
                    "O_ADDRS[" + i + "] = " + toAddr(expr.base) + " /\\ " + 
                    "P_NAMES[" + i + "] = " + mznLiteral(v) + 
                    " else del_prop_at(" + i + ") endif;\n";
            }
        }
        else {
            // Unknown offset
            preProcess(expr.base, model);
            preProcess(expr.offset, model);
            // FIXME: Adding all the builtins may be too much!
//            model.N_IMPL_PROPS++;
//            model.body += "constraint set_all_builtins(" + 
//                toTypeSvalAddr(expr.base) + ", " + model.N_IMPL_PROPS + ");\n";
//            model.N_IMPL_PROPS += STR_BUILTINS + ARRAY_BUILTINS;
            const offset_TYPE = new Type(expr.offset.type);
            if (offset_TYPE.has(Type.OBJECT)) {
                // Unknown base.
                const t = toType(expr.base);
                if (!["Null", "Undef", "Bool", "Num", "Str", "Array"].includes(t)) {
                    model.N_IMPL_PROPS++;
                    const i = model.N_IMPL_PROPS;
                    model.body +=
                        "constraint if " + t + " = Object then " + 
                        "O_ADDRS[" + i + "] = " + toAddr(expr.base) + " /\\ " + 
                        "P_NAMES[" + i + "] = " + toSval(expr.offset) + 
                        " else del_prop_at(" + i + ") endif;\n";
                }
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
        if (expr.op === "+" && (toType(expr.left) !== "Num" 
        || toType(expr.right) !== "Num"))
            add_tmp_addr(expr, model)
        preProcess(expr.left, model);
        preProcess(expr.right, model);
    }
    else if (expr instanceof ToBoolean) {
        preProcess(expr.value, model);
    }
    else if (expr instanceof StringIndexOf) {
        model.body += "constraint " + toType(expr.base) + " = Str;\n"
        preProcess(expr.searchString, model);
        preProcess(expr.base, model);
        preProcess(expr.offset, model);
        preProcess(expr.start, model);        
    }
    else if (expr instanceof StringRepeat) {
        model.body += "constraint " + toType(expr.base) + " = Str /\\ is_nat("
            + toNum(expr.num) + ");\n";
        preProcess(expr.num, model);
        preProcess(expr.base, model);
        add_tmp_addr(expr, model);
    }
    else if (expr instanceof StringCharAt) {
        model.body += "constraint " + toType(expr.base) + " = Str;\n"
        preProcess(expr.idx, model);
        preProcess(expr.base, model);
        add_tmp_addr(expr, model);
    }
    else if (expr instanceof StringConcat) {
         model.body += "constraint " + toType(expr.base) + " = Str;\n"
        preProcess(expr.base, model);
        preProcess(expr.args, model);
        add_tmp_addr(expr, model);
    }
    else if (expr instanceof StringSlice) {
         model.body += "constraint " + toType(expr.base) + " = Str;\n"
        preProcess(expr.base, model);
        preProcess(expr.start, model);
        preProcess(expr.end, model);
        add_tmp_addr(expr, model);
    }
    else if (expr instanceof StringIncludes) {
        model.body += "constraint " + toType(expr.base) + " = Str;\n"
        preProcess(expr.base, model);
        preProcess(expr.searchString, model);
    }
    else if (expr instanceof StringSplit) {
        model.body += "constraint " + toType(expr.base) + " = Str;\n"
        preProcess(expr.base, model);
        preProcess(expr.sep, model);
        add_tmp_addr(expr, model);
    }
    else if (expr instanceof StringSubstr) {
        model.body += "constraint " + toType(expr.base) + " = Str;\n"
        preProcess(expr.base, model);
        preProcess(expr.start, model);
        preProcess(expr.len, model);
        add_tmp_addr(expr, model);
    }
    else if (expr instanceof StringToLowerCase 
          || expr instanceof StringToUpperCase) {
        model.body += "constraint " + toType(expr.base) + " = Str;\n"
        preProcess(expr.base, model);
    }
    else if (expr instanceof StringCharCodeAt) {
        model.body += "constraint " + toType(expr.base) + " = Str;\n"
        preProcess(expr.base, model);
        preProcess(expr.idx, model);
    }
    else if (expr instanceof ArrayIncludes) {
        model.body += "constraint " + toType(expr.base) + " = Array;\n"
        preProcess(expr.base, model);
        preProcess(expr.searchItem, model);
        if (!(expr.base instanceof Constant)) {
            model.N_IMPL_PROPS++;
            model.body += "constraint set_array_builtins(" + 
                toTypeSvalAddr(expr.base) + ", " + model.N_IMPL_PROPS + ");\n";
            model.N_IMPL_PROPS += ARRAY_BUILTINS;
        }
    }
    else if (expr instanceof MathAbs || expr instanceof MathCeil || 
           expr instanceof MathFloor || expr instanceof MathSqrt) {
        preProcess(expr.num, model);
    }
    else if (expr instanceof NumberToFixed) {
        preProcess(expr.base, model);
        preProcess(expr.fracDigits, model);
        add_tmp_addr(expr, model);
    }
    else if (expr instanceof NumberIsFinite || expr instanceof NumberIsNaN 
          || expr instanceof IsFinite || expr instanceof IsNaN)
        preProcess(expr.val, model);
    else if (expr instanceof RegExpTest) {
        preProcess(expr.str, model);
    }
    else if (expr instanceof RegExpExec) {
//        console.log(expr)
        preProcess(expr.str, model);
        const id = expr._resultObjId, regexId = "regexId" + id;
        // FIXME: Not sure of this! Why different RegExpExec have same _resultObjId?
        if (!model.REGEX_ID.has(id)) {
            model.REGEX_ID.add(id);
            model.body += "var {0," + id + "}: " + regexId + ";\n";
        }
        model.body += "constraint " + regexId + " = " + id + " * (" + 
            mznRegExp(expr._formula) + ");\nconstraint " + 
            mznRegExp(expr.toBooleanFormula()) + ";\n";
    }
    else if (expr instanceof ToString)
        preProcess(expr.value, model);
    else if (expr instanceof ToObject) {
        model.N_ADDRS++;
        preProcess(expr.value, model);
    }
    else if (expr instanceof StringToString)
        preProcess(expr.base, model);   
}

function mznLiteral(x) {
    if (typeof x !== "string")
        return "\"" + x + "\"";
    let s = "";
    let ascii = true;
    for (let i = 0; i < x.length; ++i) {
        const ch = x.charCodeAt(i);
        if (ch < 32 || (ch > 127 && ch < 256)) {
            ascii = false;            
            if (ch < 16)
                s += ("\\x0" + ch.toString(16)).slice(-4);
            else
                s += ("\\x" + ch.toString(16)).slice(-4);
        }
        else if (ch > 256) {
            console.log("Warning! G-Strings does not fully support yet UTF-16.")
            const c = "\\x" + ((ch.toString(16)).slice(-2));
            console.log("Replacing " + x[i] + " with " + c);
            ascii = false;            
            s += c;
        }
    }
    if (ascii)
        return "\"" + x + "\"";
    else
        return "\"" + s + "\"";
}

function escapeRegExp(x) {
    return x.replace(/\\[^tnabvfrxuUe]/g, "\\").replace(/\./g, "\\.").
        replace(/\(/g, "\\(").replace(/\)/g, "\\)").replace(/\*/g, "\\*").
        replace(/\[/g, "\\[").replace(/\]/g, "\\]").replace(/\|/g, "\\|");
}

function mznRegExpBound(re) {
    let x = re.substr(1, re.length - 2);
    if (x[0] === '\\' && x.length < 4 && /^\d$/.test(x[1]))
        x = "\\x0" + x[2];
    return x;
}

//const DOT = 're.union,re.range,"\\x00","\\x09",re.range,"\\x0B","\\x0C",re.range,"\\x0E","\\xFF"';
function mznRegExp(re) {
  switch (re) {
      case "re.allchar":
          return "(.*)";      
      default:          
          if (typeof(re) === "string" && (re.startsWith("var")
          || re.startsWith("regex_exec_") || re.startsWith("regex_capture_")))
              return "SVAL_" + re;
  }
  switch (re[0]) {
      case "Str":
          return "(" + mznRegExp(re[1]) + ")";
      case "str.in.re":
          return "str_reg(" + mznRegExp(re[1]) +", \""+ mznRegExp(re[2]) +"\")";
      case "str.to.re":
          return "(" + escapeRegExp(re[1].substr(1, re[1].length - 2)) + ")";
      case "str.++":
          let rs = "(";
          const ns = re.length - 1;
          for (let i = 1; i < ns; ++i)
              rs += mznRegExp(re[i]) + " ++ ";
          return rs + mznRegExp(re[ns]) + ")";
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
//          if (String(re[1]) === DOT) {
//              const a = "\\x00", b = "\\xFF"
//              if (typeof(u) === "number")
//                  return "[" + a + "-" + b + "," + l + "," + u + "]";
//              else
//                  return "[" + a + "-" + b + "," + l + "]";
//          }
          let r1 = mznRegExp(re[1]), r2 = "(" + r1.repeat(l) + ")";
          if (typeof(u) === "number")
              r2 += "(" + ("(" + r1 + "|())").repeat(u - l) + ")";
          else
              r2 += "(" + r1 + ")*";
          return r2;
      case "re.inter":
          let ri = "(";
          const m = re.length - 1;
          for (let i = 1; i < m; ++i)
              ri += mznRegExp(re[i]) + "&"
          return ri + mznRegExp(re[m]) + ")";
      case "=":
          return "(" + mznRegExp(re[1]) + " = " + mznRegExp(re[2]) + ")";
      case "and":
          let ra = "(";
          const na = re.length - 1;
          for (let i = 1; i < na; ++i)
              ra += mznRegExp(re[i]) + " /\\ ";
          return ra + mznRegExp(re[na]) + ")";
      case "ite":
          return "[" + mznRegExp(re[3]) + ", " + mznRegExp(re[2]) + 
              "][" + mznRegExp(re[1]) + " + 1]";
      default:
          throw new Error("Unsupported regex! " + re)
  }
}

function fromTSA(expr, suff) {
    if (expr instanceof Constant) {
        if (suff == "TYPE")
            return expr.value === null ? "Null" : JSPrimitive[expr.getType()]
        else if (suff == "SVAL")
            return mznLiteral(expr.value)
        else
            return typeof(expr.value) === "object" && expr.value !== null ? 
              expr.objectId + 1 : "0";
    }
    else if (expr instanceof Variable || expr instanceof Temporary)
        return suff + "_" + expr.name
    else if (expr instanceof GetField) {
        if (expr.base instanceof Constant) {
            // Wrappers and constant objects.
            const v = expr.base.value;
            const w = mznLiteral(v)
            switch (typeof(v)) {
                case "string":
                    return "P_" + suff + "S[get_str_prop("  + w + ", " + 
                        toSval(expr.offset) + ", )]";
                case "number":
                    return "P_" + suff + "S[get_num_prop("  + w + ", " + 
                        toSval(expr.offset) + ", )]";
                case "boolean":
                    return "P_" + suff + "S[get_bool_prop(" + w + ", " +
                        toSval(expr.offset) + ", )]";
//                case "function":
                default:
                    const val = "P_" + suff + "S[get_prop(Object, " + 
                        (expr.base.objectId + 1) + ", " + toSval(expr.offset) + 
                        ", N_IMPL_PROPS)]";                    
                    if (v instanceof Array) {
                        if (suff === "TYPE")
                            return "if " + toSval(expr.offset) + ' = "length" then Num else ' + val + ' endif';
                        else if (suff === "SVAL")
                            return "if " + toSval(expr.offset) + ' = "length" then "' + v.length + '" else ' + val + ' endif';
                        else
                            return "if " + toSval(expr.offset) + ' = "length" then 0 else ' + val + ' endif';
                    }
                    //FIXME: builtin objects, e.g. Math?
                    return val;
            }
        }
        else {
            if (/var\d/.test(expr.base) && FIRST_GET[expr.base] === undefined)
                FIRST_GET[expr.base] = N_WRITES;
            const id = TMP_ADDR[toSval(expr.base)];
            if (id === undefined)
                return "P_" + suff + "S[get_prop(" + toTypeAddr(expr.base) + ", " 
                    + toSval(expr.offset) + ", N_IMPL_PROPS + " + N_WRITES + ")]";
            else
                return "P_" + suff + "S[get_prop(" + toType(expr.base) + ", " 
                    + id + ", " + toSval(expr.offset) + ", N_IMPL_PROPS + " + N_WRITES + ")]";
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
            return "tmp_str_arr()"; //FIXME: Array representation is over-approximated!
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
            return "0"
    }
    else if (expr instanceof StringIncludes) {
        if (suff === "TYPE")
            return "Bool";
        else if (suff === "SVAL")
            return "str_find(" + toSval(expr.searchString) + ", " 
                + toSval(expr.base) + ") > 0";
        else if (suff === "ADDR")
            return "0";
    }
    else if (expr instanceof ArrayIncludes) {
        if (suff === "TYPE")
            return "Bool";
        else if (suff === "SVAL")
            return "array_includes(" + toAddr(expr.base) + ", "
                + toTypeSvalAddr(expr.searchItem) + ", N_IMPL_PROPS + " 
                + N_WRITES + ")";
        else if (suff === "ADDR")
            return "0";
    }
    else if (expr instanceof StringRepeat) {
        if (suff === "TYPE")
            return "Str";
        else if (suff === "SVAL") {
            const i = toNum(expr.num);
            const j = isNaN(Number(expr.num)) ? 
                "str2nat(" + i + ")" : i.slice(1, i.length - 1);
            return "str_pow(" + toSval(expr.base) + ", " + j + ")";
        }
        else
            return TMP_ADDR[expr] === undefined ? "0" : TMP_ADDR[expr];
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
            return TMP_ADDR[expr] === undefined ? "0" : TMP_ADDR[expr];
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
            return TMP_ADDR[expr] === undefined ? "0" : TMP_ADDR[expr];
    }
    else if (expr instanceof StringSlice) {
        if (suff === "TYPE")
            return "Str"
        else if (suff === "SVAL")
            return "js_str_slice(" + toSval(expr.base) + ", " 
                + toNum(expr.start) + ", " + toTypeSval(expr.end) + ")";
        else
            return TMP_ADDR[expr] === undefined ? "0" : TMP_ADDR[expr];
    }
    else if (expr instanceof StringSplit) {
       if (suff === "TYPE")
           return "Array";
       if (suff === "SVAL")
           if (expr.sep instanceof Constant)
               return "js_split(" + toSval(expr.base) + ", " + toSval(expr.sep.value) + ")";
           else
               return "_";
       else
           return TMP_ADDR[expr];
    }
    else if (expr instanceof StringSubstr) {
        if (suff === "TYPE")
            return "Str"
        else if (suff === "SVAL")
            return "js_substr(" + toSval(expr.base) + ", " 
                + toNum(expr.start) + ", " + toTypeSval(expr.len) + ")";
        else
            return TMP_ADDR[expr] === undefined ? "0" : TMP_ADDR[expr];
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
        const regexId = "regexId" + expr._resultObjId;
        if (suff === "TYPE")
            return "[Null, Array][(" + regexId + " > 0) + 1]";
        else if (suff === "SVAL")
            return '["null", tmp_str_arr()][(' + regexId + ' > 0) + 1]';
        else
            return regexId;
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
            return TMP_ADDR[expr] === undefined ? "0" : TMP_ADDR[expr];
    }
    else if (expr instanceof NumberIsFinite || expr instanceof IsFinite) {
        if (suff === "TYPE")
            return "Bool";
        else if (suff === "SVAL")
            return "is_finite(" + toTypeSval(expr.val) + ")";
        else
            return "0";
    }
    else if (expr instanceof NumberIsNaN || expr instanceof IsNaN) {
        if (suff === "TYPE")
            return "Bool";
        else if (suff === "SVAL")
            return "is_nan(" + toTypeSval(expr.val) + ")";
        else
            return "0";
    }
    else if (expr instanceof ToString) {
        if (suff === "TYPE")
            return "Str";
        else if (suff === "SVAL")
            return toSval(expr.value);
        else
            return toAddr(expr.value);
    }
    else if (expr instanceof StringToString) {
        if (suff === "TYPE")
            return "Str";
        else if (suff === "SVAL")
            return toSval(expr.base);
        else
            return toAddr(expr.base);
    }
    else if (expr instanceof StringToLowerCase) {
        if (suff === "TYPE")
            return "Str";
        else if (suff === "SVAL")
            return "str_lcase(" + toSval(expr.base) + ")";
        else
            return TMP_ADDR[expr] === undefined ? "0" : TMP_ADDR[expr];
    }
    else if (expr instanceof StringToUpperCase) {
        if (suff === "TYPE")
            return "Str";
        else if (suff === "SVAL")
            return "str_ucase(" + toSval(expr.base) + ")";
        else
            return TMP_ADDR[expr] === undefined ? "0" : TMP_ADDR[expr];
    }
    else if (expr instanceof StringCharCodeAt) {
        if (suff === "TYPE")
            return "Num";
        else if (suff === "SVAL")
            return "js_char_code_at(" + toSval(expr.base) + ", " 
                                      + toNum(expr.idx) + ")";
        else
            return "0";
    }
    else if (expr instanceof ToObject) {
        if (suff === "TYPE")
            return "Object";
        else if (suff === "SVAL")
            return toSval(expr.value); //FIXME: Explicit wrapper Objects handled yet.
        else
            return expr.id;
    }
    else {
        console.log(expr)
        throw new Error("Unsupported: " + expr);
    }
}

function toTSA(x) {
    if (x === null) {
        return "Null, \"null\", 0";
    }
    switch (typeof(x)) {
        case "function": // FIXME: just so we don't get spurious exceptions on objects with methods
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
    return toType(x) + ", "  + toSval(x)
}
function toTypeAddr(x) {
    return toType(x)  + ", "  + toAddr(x)
}
function toTypeSvals(x, y) {
    return toTypeSval(x) + ", "  + toTypeSval(y)
}
function toTypeSvalAddr(x) {
    return toTypeSval(x)  + ", " + toAddr(x);
}
function toTypeSvalAddrs(x, y) {
    return toTypeSvalAddr(x)  + ", "  + toTypeSvalAddr(y);
}

function toBool(x) {
    const tx = toType(x);
    const sx = toSval(x);
    return tx === "Bool" ? sx : "to_bool_var(" + tx + ", " + sx + ")";
}
function toNum(x) {
    const t = toType(x);
    const s = toSval(x);
    if (t === "Num") {
        const ns = +(s.slice(1, s.length - 1));
        if (isFinite(ns)) {
            if (ns < MIN_INT) {
                console.warn("Warning: integer literal " + s + " is too small");
                console.warn("Changed to -Infinity.");
                return '"-Infinity"';
            }
            if (ns > MAX_INT) {
                console.warn("Warning: integer literal " + s + " is too big");
                console.warn("Changed to Infinity.");
                return '"Infinity"';
            }
        }
        return s;
    }
    return "to_num(" + t + ", " + s + ")";
}
function toNum0(x) {
    const t = toType(x);
    const s = toSval(x);
    if (t === "Num") {
        const ns = +(s.slice(1, s.length - 1));
        if (isFinite(ns)) {
            if (ns < MIN_INT) {
                console.warn("Warning: integer literal " + s + " is too small");
                console.warn("Changed to -Infinity.");
                return '"-Infinity"';
            }
            if (ns > MAX_INT) {
                console.warn("Warning: integer literal " + s + " is too big");
                console.warn("Changed to Infinity.");
                return '"Infinity"';
            }
        }
        return s;
    }
    return "to_num0(" + t + ", " + s + ")";
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
    if (op === "+")
         return "plus_SVAL(" + toTypeSvals(x, y) + ")";
    const nx = toNum(x);
    const ny = op === "/" ? toNum(y) : toNum0(y);
    if (nx === "NaN" || ny === "NaN")
        return "NaN";
     switch (op) {
         case "-":
            if (nx === '"0"')
                return negate(ny);
            if (ny === '"0"')
                return nx;
            return "sub(" + nx + ", " + ny + ")";
         case "*":
            if (nx === '"1"')
                return ny;
            if (ny === '"1"')
                return nx;
            return "mul(" + nx + ", " + ny + ")";
         case "/":
            if (ny === '"1"')
                return nx;
            return "divs(" + nx + ", " + ny + ")";
         case "%":
            if (nx === '"0"' || nx === '"1"')
                return nx;
            return "mods(" + nx + ", " + ny + ")";
     }
 }

function binaryOpToMZN(op, left, right, suff) {
    switch (suff) {
        case "TYPE": {
            switch (op) {
                case "+":
                    const lhs = toType(left);
                    const rhs = toType(right);
                    if (['Null', 'Undef', 'Bool', 'Num'].includes(lhs) && 
                        ['Null', 'Undef', 'Bool', 'Num'].includes(rhs))
                        return "Num";
                    else if (lhs === "Str" || rhs === "Str")
                        return "Str";
                    else
                        return "plus_TYPE(" + toTypes(left, right) + ")";
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
                    const lhs = toType(left);
                    const rhs = toType(right);
                    if (['Null', 'Undef', 'Bool', 'Num'].includes(lhs) && 
                        ['Null', 'Undef', 'Bool', 'Num'].includes(rhs))
                        return "add(" + toNum(left) + ", " + toNum(right) + ")";
                    else
                    if (lhs === "Str" || rhs === "Str")
                        return toSval(left) + " ++ " + toSval(right);
                    else
                        return arithBop(op, left, right);
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
                    return "0";
            }
        }
    }
    throw new Error("Unsupported binary: " + op);
}

function notBinaryRelToMZN(op, left, right) {
    const tx = toType(left);
    const sx = toSval(left);
    const nx = +(sx.slice(1, sx.length - 1));
    const ty = toType(right);
    const sy = toSval(right);
    const ny = +(sy.slice(1, sy.length - 1));
    if (tx === "Num" && isFinite(nx) && (nx < MIN_INT || nx > MAX_INT)) {
        op[1] = op[1] == "<" ? ">" : "<"; 
        return "not_" + longIntBinaryRel(op, sy, sx);
    }
    if (ty === "Num" && isFinite(ny) && (ny < MIN_INT || ny > MAX_INT))
        return "not_" + longIntBinaryRel(op, sx, sy);
    switch (op) {
        case "<":
            return "not_lt(" + tx + ", " + sx + ", " + ty + ", " + sy + ")";
        case "<=":
            return "not_le(" + tx + ", " + sx + ", " + ty + ", " + sy + ")";
        case ">":
            return "not_lt(" + ty + ", " + sy + ", " + tx + ", " + sx + ")";
        case ">=":
            return "not_le(" + ty + ", " + sy + ", " + tx + ", " + sx + ")";
        default:
            return not(binaryRelToMZN(op, left, right, tx, sx, ty, sy))
    };
}

function binaryRelToMZN(op, left, right, tx, sx, ty, sy) {
    if (tx === undefined)
        tx = toType(left);
    if (sx === undefined)
        sx = toSval(left);
    if (ty === undefined)
        ty = toType(right);
    if (sy === undefined)
        sy = toSval(right);
    const nx = +(sx.slice(1, sx.length - 1));
    const ny = +(sy.slice(1, sy.length - 1));
    if (tx === "Num" && isFinite(nx) && (nx < MIN_INT || nx > MAX_INT)) {
        op[1] = op[1] == "<" ? ">" : "<"; 
        return longIntBinaryRel(op, sx, sy);
    }
    if (ty === "Num" && isFinite(ny) && (ny < MIN_INT || ny > MAX_INT))
        return longIntBinaryRel(op, sx, sy);
    switch (op) {
        case "<":
            if (["Null", "Undef", "Bool", "Num"].includes(tx) ||
                ["Null", "Undef", "Bool", "Num"].includes(ty))
                return "lt_num(" + sx + ", " + sy + ")";
            else
                return "lt(" + tx + ", " + sx + ", " + ty + ", " + sy + ")";
        case "<=":
            if (["Null", "Undef", "Bool", "Num"].includes(tx) ||
                ["Null", "Undef", "Bool", "Num"].includes(ty))
                return "le_num(" + sx + ", " + sy + ")";
            else
                return "le(" + tx + ", " + sx + ", " + ty + ", " + sy+ ")";
        case ">":
            if (["Null", "Undef", "Bool", "Num"].includes(tx) ||
                ["Null", "Undef", "Bool", "Num"].includes(ty))
                return "lt_num(" + sy + ", " + sx + ")";
            else
                return "lt(" + ty + ", " + sy + ", " + tx + ", " + sx + ")";
        case ">=":
            if (["Null", "Undef", "Bool", "Num"].includes(tx) ||
                ["Null", "Undef", "Bool", "Num"].includes(ty))
                return "le_num(" + sy + ", " + sx + ")";
            else
                return "le(" + ty + ", " + sy + ", " + tx + ", " + sx + ")";
        case "==":
            if (tx === ty) {
                switch(tx) {
                    case "Null":
                    case "Undef":
                        return "true";
                    case "Bool":
                    case "Str":
                        return sx + " = " + sy;
                    case "Num":
                        return sx + " = " + sy + " /\\ " + sx + " != \"NaN\"";
                    case "Object":
                        return toAddr(left) + " = " + toAddr(right);
                    case "Array":
                        return "(" + toAddr(left) + " = " + toAddr(right) + " \\/ "
                            + "(" + sx + " = \"\" /\\ " + sy + " = \"\"))";
                    default:
                        return "abstract_eq(" + tx + ", " + sx + ", " + toAddr(left)  + ", "
                                  + ty + ", " + sy + ", " + toAddr(right) + ")";
                }
            }
            return "abstract_eq(" + tx + ", " + sx + ", " + toAddr(left)  + ", "
                                  + ty + ", " + sy + ", " + toAddr(right) + ")";
        case "===":
            return "strict_eq(" + tx + ", " + sx + ", " + toAddr(left)  + ", "
                                + ty + ", " + sy + ", " + toAddr(right) + ")";
        case "!=":
            if (tx === ty) {
                switch(tx) {
                    case "Null":
                    case "Undef":
                        return "false";
                    case "Bool":
                    case "Str":
                        return sx + " != " + sy;
                    case "Num":
                        return "((" + sx + " = " + sy + ") -> (" + sx + " = \"NaN\"))";
                    case "Object":
                        return toAddr(left) + " != " + toAddr(right);
                    case "Array":
                        return "((" + toAddr(left) + " = " + toAddr(right) + ") -> "
                            + "(" + sx + " != \"\" \\/ " + sy + " != \"\"))";
                    default:
                        return "not(abstract_eq(" + tx + ", " + sx + ", " + toAddr(left)  + ", "
                                  + ty + ", " + sy + ", " + toAddr(right) + "))";
                }
            }
            return "not(abstract_eq(" + tx + ", " + sx + ", " + toAddr(left)  + ", "
                                      + ty + ", " + sy + ", " + toAddr(right) + "))";
        case "!==":
            return "not(strict_eq(" + tx + ", " + sx + ", " + toAddr(left) + ", "
                                    + ty + ", " + sy + ", " + toAddr(right) + "))";
        case "in":
            return "is_def("+ sx + ", " + ty + ", " + toAddr(right) + ")";
        default:
            return "to_bool_var(" + binaryOpToMZN(op, left, right, "TYPE") + ", " 
                                  + binaryOpToMZN(op, left, right, "SVAL") + ")";
    }
}

function longIntBinaryRel(op, x, w) {
    switch (op) {
        case "<":
            return "lt_int_no32(" + x + ", " + w + ")";
        case "<=":
            return "le_int_no32(" + x + ", " + w + ")";
        case ">":
            return "gt_int_no32(" + x + ", " + w + ")";
        case ">=":
            return "ge_int_no32(" + x + ", " + w + ")";
        default:
            throw new Error("Unsupported operand! " + op);
    };
}

exports.addMiniZincConstraint = addMiniZincConstraint; 









