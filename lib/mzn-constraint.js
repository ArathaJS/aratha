const {
    Unary, Binary, Variable, Constant, GetField, PutField, DeleteField, 
    StringCharAt, StringIndexOf, StringConcat, StringSlice, 
    NewArray, RegExpTest
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

//TODO: Add more built-in properties. 
const BUILTIN_PROPS = new Set([
  "length", "__proto__", "constructor", 
])

function isIndex(n) {
    return (String(n) === "0") || (/^[1-9]\d*$/.test(n));
}

function toMZNConstraint(cons, solver) {
    var smt_cons = //"% SMT constraint: " + cons + 
    "\nconstraint "
//    console.log(smt_cons)
    if (cons instanceof Array)
        switch (cons[0]) {
            case 'is-Str':
                return smt_cons + "TYP_" + cons[1] + " = Str";
            case 'is-Num':
                return smt_cons + "TYP_" + cons[1] + " = Num";    
            default:
                throw new Error("Unsupported: " + cons);
        }
    if (cons instanceof TypeConstraint)
        return smt_cons + (cons.value ? 
            toTyp(cons.subject) + " in " + cons.type.toJSType() :
            "not(" + toTyp(cons.subject) + " in " + cons.type.toJSType() + ")");
    var mzn_cons = "";
    const expr = cons.expr;
    preProcess(expr, solver);
    if (expr instanceof Unary)
        mzn_cons += unaryRelToMZN(expr.op, expr.expr, solver);    
    else if (expr instanceof Binary) {
        if (cons.value || !["<", "<=", ">=", ">"].includes(expr.op))
            mzn_cons += binaryRelToMZN(expr.op, expr.left, expr.right, solver);
        else
            return smt_cons + 
                   notBinaryRelToMZN(expr.op, expr.left, expr.right, solver);
    }
    else {
        console.log(expr)
        throw new Error("Unsupported: " + expr);
    }
    return smt_cons + (cons.value ? mzn_cons : not(mzn_cons));
}

function preProcess(expr, solver) {
    if (expr instanceof NewArray) {
        solver.N_LOCS++;
        solver.MIN_LOC++;
        solver.N_IMPL_PROPS++;
        solver.mznHead += "constraint set_prop_at(" + expr.id + ", \"0\", " + 
            toTypRepLoc(expr.value) + ", " + solver.N_IMPL_PROPS + ");\n";        
    }
    else if (expr instanceof Constant && typeof(expr.value) === "object") {
        solver.N_LOCS++;
        solver.MIN_LOC++;
        const id = expr.objectId + 1;
        for (var key in expr.value) {
            solver.N_IMPL_PROPS++;
            solver.mznHead += "constraint set_prop_at(" + id + ", \"" + 
                key + "\", " + toTRL(expr.value[key]) + ", " + 
                solver.N_IMPL_PROPS + ");\n";                             
        }
    }
    else if (expr instanceof GetField) {
        if (expr.base instanceof Constant) {
            preProcess(expr.offset, solver);
            // Wrappers and constant objects.
            const v = expr.base.value;
            if (typeof(v) === "object") {
                const id = expr.base.objectId + 1;
                for (var key in v) {
                    solver.N_IMPL_PROPS++;
                    solver.mznHead += "constraint set_prop_at(" + id + ", \"" 
                        + key + "\", " + toTRL(expr.base.value[key]) + ", " + 
                        solver.N_IMPL_PROPS + ");\n";                             
                }
            }
            else
                solver.N_IMPL_PROPS++;
        }
        else if (expr.base instanceof PutField) {
            preProcess(expr.base, solver);
            preProcess(expr.offset, solver);
        }
        else if (expr.offset instanceof Constant) {    
            // Setting built-in properties, including index access.
            preProcess(expr.base, solver);
            const v = expr.offset.value;
            solver.N_IMPL_PROPS++;
            if (BUILTIN_PROPS.has(v))
                solver.mznHead += "constraint set_builtin_prop(" + 
                    toLoc(expr.base) + ", \"" + v + "\", " + toTypRep(expr.base)
                    + ", " + solver.N_IMPL_PROPS + ");\n";
            else if (isIndex(v))
                solver.mznHead += "constraint set_access_builtin(" + 
                    toLoc(expr.base) + ", " + v + ", " + toTypRep(expr.base)
                    + ", " + solver.N_IMPL_PROPS + ");\n";
            else {
                // Unknown base.
                const i = solver.N_IMPL_PROPS;
                solver.mznHead +=
                    "constraint if is_obj(" + toTyp(expr.base) + ") then " + 
                    "LOCS[" + i + "] = " + toLoc(expr.base) + " /\\ " + 
                    "KEYS[" + i + "] = \"" + v + "\" else del_prop_at(" + i + 
                    ") endif;\n";
            }
        }
        else {
            // Unknown offset, add all the builtins.
            preProcess(expr.base, solver);
            preProcess(expr.offset, solver);
            const offset_type = new Type(expr.offset.type);
            if (offset_type.has(Type.BOOLEAN)) {
                solver.mznHead += "constraint set_bool_builtins(" 
                    + toLoc(expr.base) + ", " + toTyp(expr.base) + ", " + 
                      toRep(expr.base) + ", " + (solver.N_IMPL_PROPS + 1) + ");\n";
                solver.N_IMPL_PROPS += BOOL_BUILTINS;
            }
            if (offset_type.has(Type.NUMBER)) {
                solver.mznHead += "constraint set_num_builtins(" 
                    + toLoc(expr.base) + ", " + toTyp(expr.base) + ", " + 
                      toRep(expr.base) + ", " + (solver.N_IMPL_PROPS + 1) + ");\n";
                solver.N_IMPL_PROPS += NUM_BUILTINS;
            }
            if (offset_type.has(Type.STRING)) {
                solver.mznHead += "constraint set_str_builtins(" 
                    + toLoc(expr.base) + ", " + toTyp(expr.base) + ", " + 
                      toRep(expr.base) + ", " + (solver.N_IMPL_PROPS + 1) + ");\n";
                solver.N_IMPL_PROPS += STR_BUILTINS;
            }
            if (offset_type.has(Type.OBJECT)) {
                // Unknown base.
                solver.N_IMPL_PROPS++;
                const i = solver.N_IMPL_PROPS;
                solver.mznHead +=
                    "constraint if is_obj(" + toTyp(expr.base) + ") then " + 
                    "LOCS[" + i + "] = " + toLoc(expr.base) + " /\\ " + 
                    "KEYS[" + i + "] = " + toRep(expr.offset) + 
                    " else del_prop_at(" + i + ") endif;\n";
            }
        }
    }
    else if (expr instanceof PutField) {
        preProcess(expr.base, solver);
        preProcess(expr.offset, solver);
        preProcess(expr.val, solver);
        solver.N_EXPL_PROPS++;
        solver.MIN_LOC++;
        solver.N_LOCS++;        
    }
    else if (expr instanceof DeleteField) {        
        preProcess(expr.base, solver);
        preProcess(expr.offset, solver);
        solver.N_EXPL_PROPS++;
    }
    else if (expr instanceof Unary)
        preProcess(expr.expr, solver);
    else if (expr instanceof Binary) {
        preProcess(expr.left, solver);
        preProcess(expr.right, solver);
    }
}

function mznLiteral(x) {
    var s = "";
    var ascii = true;
    for (var i = 0; i < x.length; ++i) {
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
    //TODO:
    return x;
} 

function mznRegExp(re) {
//  console.log(re)
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
          var rc = "(";
          for (var i = 1; i < re.length; ++i)
              rc += mznRegExp(re[i]);
          return rc + ")";
      case "re.union":
          var ru = "(";
          const n = re.length - 1;
          for (var i = 1; i < n; ++i)
              ru += mznRegExp(re[i]) + "|"
          return ru + mznRegExp(re[n]) + ")";
      case "re.range":
          return "[" + re[1].substr(1, re[1].length - 2) + "-" 
                     + re[2].substr(1, re[2].length - 2) + "]";
      default:
          throw new Error("Unsupported regex! " + re)
  }
}

function fromTRL(expr, suff) {
    if (expr instanceof Constant) {
        if (suff == "TYP")
            return expr.value === null ? "Null" : JSPrimitive[expr.getType()]
        else if (suff == "REP") {
            if (typeof expr.value === String)
                return mznLiteral(expr.value)
            else
                return "\"" + expr.value + "\""
        }
        else
            return typeof(expr.value) === "object" && expr.value !== null ? 
              expr.objectId + 1 : "0";
    }
    else if (expr instanceof Variable) {
        if (suff === "REF")
           return "LOC_" + expr.name
        else  
           return suff + "_" + expr.name
    }
    else if (expr instanceof GetField) {
        if (expr.base instanceof Constant) {
            // Wrappers and constant objects.
            const v = expr.base.value;
            switch (typeof(v)) {
                case "string":
                    return suff + "S[get_str_prop(\"" + v + "\", " + 
                        toRep(expr.offset) + ", )]";
                case "number":
                    return suff + "S[get_num_prop(\"" + v + "\", " + 
                        toRep(expr.offset) + ", )]";
                case "boolean":
                    return suff + "S[get_bool_prop(\"" + v + "\", " +
                        toRep(expr.offset) + ", )]";
//                case "function":
                default:
                    //FIXME: builtin objects, e.g. Math?
                    return suff + "S[get_prop(Object, " + (expr.base.objectId + 1) + 
                        ", " + toRep(expr.offset) + ", )]";
            }
        }
        else return suff + "S[get_prop(" + toTypLoc(expr.base) + ", " + 
            toRep(expr.offset) + ")]";
    }
    else if (expr instanceof PutField) {
        if (suff === "REF")
            return "put_prop(" + toTypLoc(expr.base) + ", " + toRep(expr.offset)
                + ", " + toTypRepLoc(expr.val) + ")";
        else
            return fromTRL(expr.base, suff)
    }
    else if (expr instanceof DeleteField) {
        if (suff === "REF")
            return "del_prop(" + toTypLoc(expr.base) + ", " + toRep(expr.offset)
                 + ")";
        else
            return fromTRL(expr.base, suff)
    }
    else if (expr instanceof Unary)
        return unaryOpToMZN(expr.op, expr.expr, suff);
    else if (expr instanceof Binary)
        return binaryOpToMZN(expr.op, expr.left, expr.right, suff);
    else if (expr instanceof NewArray) {
        if (suff === "TYP")
            return "Array";
        else if (suff === "REP")
            return "FIXME: Array representation to be done!";
        else
            return expr.id;
    }
    else if (expr instanceof StringIndexOf) {
        if (suff === "TYP")
            return "Num";
        else if (suff === "REP") {
            const x = toRep(expr.searchString);
            const y = toRep(expr.base);
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
        if (suff === "TYP")
            return "Str"
        else if (suff === "REP") {
            const i = toNum(expr.idx);
            const j = isNaN(Number(expr.idx)) ? 
                "str2nat(" + i + ")" : i.slice(1, i.length - 1);
            return "str_char_at(" + toRep(expr.base) + ", " + j + " + 1)";
        }
        else
            return "0"
    }
    else if (expr instanceof StringConcat) {
        if (suff === "TYP")
            return "Str"
        else if (suff === "REP") {          
            const args = expr.args, n = args.length - 1;
            var c = toRep(expr.base) + " ++ ";
            for (var i = 0; i < n; ++i)
                c += toRep(args[i]) + " ++ ";
            return c + toRep(args[n]);
        }
        else
            return "0"
    }
    else if (expr instanceof StringSlice) {
        if (suff === "TYP")
            return "Str"
        else if (suff === "REP") {          
            const i0 = toNum(expr.start);
            const j0 = isNaN(Number(i0)) ? 
                "str2nat(" + i0 + ")" : i0.slice(1, i0.length - 1);
            const i1 = toNum(expr.end);
            const j1 = isNaN(Number(i1)) ?
                "str2nat(" + i1 + ")" : i1.slice(1, i1.length - 1);
            return "str_sub(" + toRep(expr.base) + ", " + j0 + " + 1, " + j1 + ")";
        }
        else
            return "0"
    }
    else if (expr instanceof RegExpTest) {
        if (suff === "TYP")
            return "Bool";
        else if (suff === "REP")        
          return "str_reg(" + toRep(expr.str) + ", \"" + 
              mznRegExp(expr.toBooleanFormula()[2]) + "\")";
        else
            return "0";
    }
    else {
        console.log(expr)
        throw new Error("Unsupported: " + expr);
    }
}

function toTRL(x) {
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

function toTyp(x) {
    return fromTRL(x, "TYP");
}
function toRep(x) {
    return fromTRL(x, "REP");
}
function toLoc(x) {
    return fromTRL(x, "REF");
}
function toTyps(x, y) {
    return toTyp(x)  + ", "  + toTyp(y)
}
function toTypRep(x) {
    return toTyp(x)  + ", "  + toRep(x)
}
function toTypLoc(x) {
    return toTyp(x)  + ", "  + toLoc(x)
}
function toTypReps(x, y) {
    return toTypRep(x) + ", "  + toTypRep(y)
}
function toTypRepLoc(x) {
    return toTyp(x)  + ", "  + toRep(x)  + ", " + toLoc(x);
}
function toTypRepLocs(x, y) {
    return toTypRepLoc(x)  + ", "  + toTypRepLoc(y);
}

function toBool(x) {
    const tx = toTyp(x);
    const rx = toRep(x);
    return tx === "Bool" ? rx : "to_bool_var(" + tx + ", " + rx + ")";
}
function toNum(x) {
    const tx = toTyp(x);
    const rx = toRep(x);
    return tx === "Num" ? rx : "to_num(" + tx + ", " + rx + ")";
}
function toNum0(x) {
    const tx = toTyp(x);
    const rx = toRep(x);
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
            return "to_bool_var(" + unaryOpToMZN(op, arg, "TYP") + ", " 
                                  + unaryOpToMZN(op, arg, "REP") + ")";
    }
}

function unaryOpToMZN(op, arg, suff) {
    switch (suff) { 
        case "TYP": {
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
        case "REP": {
            switch (op) {
                case "typeof":
                    return "typeof(" + toTyp(arg) + ")";
                case "+":
                    return toNum(arg);
                case "-":
                    return negate(toNum(arg));
                case "!":
                    return toBool(arg);
            }
        }
        case "REF": {
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
            return "plus_REP(" + toTypReps(x, y) + ")";
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
        case "TYP": {
            switch (op) {
                case "+":
                    const lhs = toTyp(left);
                    const rhs = toTyp(right);
                    if (['Null', 'Bool', 'Num'].includes(lhs) && 
                        ['Null', 'Bool', 'Num'].includes(rhs))
                        return "Num";
                    else if (lhs === "Str" || rhs === "Str")
                        return "Str";
                    else
                        return "plus_TYP(" + toTyps(left, right) + ")";
                case "-":
                case "*":
                case "/":
                case "%":
                    return "Num";
            }
        }
        case "REP": {
            switch (op) {
                case "+":
                case "-":
                case "*":
                case "/":
                case "%":
                    return arithBop(op, left, right);
            }
        }
        case "REF": {
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
            return "not_lt(" + toTypReps(left, right) + ")";
        case "<=":
            return "not_le(" + toTypReps(left, right) + ")";
        case ">":
            return "not_lt(" + toTypReps(right, left) + ")";
        case ">=":
            return "not_le(" + toTypReps(right, left) + ")";
        default:
            return not(binaryRelToMZN(op, left, right));
    };
}

function binaryRelToMZN(op, left, right) {
    switch (op) {
        case "<":
            return "lt(" + toTypReps(left, right) + ")";
        case "<=":
            return "le(" + toTypReps(left, right) + ")";
        case ">":
            return "lt(" + toTypReps(right, left) + ")";
        case ">=":
            return "le(" + toTypReps(right, left) + ")";
        case "==":
            return "abstract_eq(" + toTypRepLocs(left, right) + ")";
        case "===":
            return "strict_eq(" + toTypRepLocs(left, right) + ")";
        case "!=":
            return "not(abstract_eq(" + toTypRepLocs(left, right) + "))";
        case "!==":
            return "not(strict_eq(" + toTypRepLocs(left, right) + "))";
        case "in":
            return "is_def("+ toRep(left) + ", " + toTypLoc(right) +")";
        default:
            return "to_bool_var(" + binaryOpToMZN(op, left, right, "TYP") + ", " 
                                  + binaryOpToMZN(op, left, right, "REP") + ")";
    }
}

exports.toMZNConstraint = toMZNConstraint; 
