const {
    Unary, Binary, Variable, Constant, GetField, PutField, DeleteField, NewArray
} = require("./symbolic");

const Type = require("./type")

const JSPrimitive = {
    1: "Undef",
    2: "Null",
    4: "Bool",
    8: "Str",
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
//    console.log("% SMT constraint: " + cons)
    var mzn_cons = "% SMT constraint: " + cons + "\nconstraint "
    if (!cons.value)
        mzn_cons += "not (";
    const expr = cons.expr;
    preProcess(expr, solver);
    if (expr instanceof Unary)
        mzn_cons += unaryRelToMZN(expr.op, expr.expr, solver);
    else if (expr instanceof Binary)
        mzn_cons += binaryRelToMZN(expr.op, expr.left, expr.right, solver);
    if (cons.value)
        return mzn_cons
    else
        return mzn_cons + ")";
}

function preProcess(expr, solver) {
    if (expr instanceof Constant && typeof(expr.value) === "object") {
        solver.NLOCS++;
        solver.MINLOC++;
    }
    if (expr instanceof GetField) {
        if (expr.base instanceof Constant) {
            // Wrappers and constant objects.
            const v = expr.base.value;
            if (typeof(v) === "object") {
                const id = expr.base.objectId + 1;
                for (var key in v) {
                    solver.NBUILTINS++;
                    solver.mzn_header += "constraint set_prop_known(" + id +
                        ", \"" + key + "\", " + toTRL(expr.base.value[key]) 
                        + ", " + solver.NBUILTINS + ");\n";                             
                }
            }
            else
                solver.NBUILTINS++;
            preProcess(expr.offset, solver);
        }
        else if (expr.base instanceof PutField) {
            solver.NWRITES++;
            preProcess(expr.offset, solver);
        }
        else if (expr.offset instanceof Constant) {        
            // Setting built-in properties, including index access.
            const v = expr.offset.value;
            if (BUILTIN_PROPS.has(v)) {
                solver.NBUILTINS++;
                solver.mzn_header += "constraint set_builtin_prop(" + 
                    toLoc(expr.base) + ", \"" + v + "\", " + toTypRep(expr.base)
                    + ", " + solver.NBUILTINS + ");\n";
            }        
            else if (isIndex(v)) {
                solver.NBUILTINS++;
                solver.mzn_header += "constraint set_access_builtin(" + 
                    toLoc(expr.base) + ", " + v + ", " + toTypRep(expr.base)
                    + ", " + solver.NBUILTINS + ");\n";
            }
            else {
                // Unknown base.
                solver.NBUILTINS++;
                const i = solver.NBUILTINS, j = i - 1;
                solver.mzn_header +=
                    "constraint if is_obj_nwrap(" + toTyp(expr.base) + 
                    ") then LOCS[" + i + "] = " + toLoc(expr.base) + 
                    " /\\ KEYS[" + i + "] = \"" + v + "\" else " + 
                    "LOCS[" + i + "] = LOCS[" + j + "] /\\ " + 
                    "KEYS[" + i + "] = KEYS[" + j + "] /\\ " + 
                    "TYPS[" + i + "] = TYPS[" + j + "] /\\ " + 
                    "REPS[" + i + "] = REPS[" + j + "] /\\ " + 
                    "REFS[" + i + "] = REFS[" + j + "] endif;\n";      
            }
            preProcess(expr.base, solver);
        }
        else {
            // Unknown offset, add all the builtins.            
            const offset_type = new Type(expr.offset.type);
            if (offset_type.has(Type.BOOLEAN)) {
                solver.mzn_header += "constraint set_bool_builtins(" 
                    + toLoc(expr.base) + ", " + toTyp(expr.base) + ", " + 
                      toRep(expr.base) + ", " + (solver.NBUILTINS + 1) + ");\n";
                solver.NBUILTINS += BOOL_BUILTINS;
            }
            if (offset_type.has(Type.NUMBER)) {
                solver.mzn_header += "constraint set_bool_builtins(" 
                    + toLoc(expr.base) + ", " + toTyp(expr.base) + ", " + 
                      toRep(expr.base) + ", " + (solver.NBUILTINS + 1) + ");\n";
                solver.NBUILTINS += NUM_BUILTINS;
            }
            if (offset_type.has(Type.STRING)) {
                solver.mzn_header += "constraint set_str_builtins(" 
                    + toLoc(expr.base) + ", " + toTyp(expr.base) + ", " + 
                      toRep(expr.base) + ", " + (solver.NBUILTINS + 1) + ");\n";
                solver.NBUILTINS += STR_BUILTINS;
            }
            if (offset_type.has(Type.OBJECT)) {
                // Unknown base.
                solver.NBUILTINS++;
                const i = solver.NBUILTINS, j = i - 1;
                solver.mzn_header +=
                    "constraint if is_obj_nwrap(" + toTyp(expr.base) + 
                    ") then LOCS[" + i + "] = " + toLoc(expr.base) + 
                    " /\\ KEYS[" + i + "] = " + toRep(expr.offset) + " else " + 
                    "LOCS[" + i + "] = LOCS[" + j + "] /\\ " + 
                    "KEYS[" + i + "] = KEYS[" + j + "] /\\ " + 
                    "TYPS[" + i + "] = TYPS[" + j + "] /\\ " + 
                    "REPS[" + i + "] = REPS[" + j + "] /\\ " + 
                    "REFS[" + i + "] = REFS[" + j + "] endif;\n";
            }
            preProcess(expr.base, solver);
            preProcess(expr.offset, solver);
        }
    }
    else if (expr instanceof PutField) {
        solver.NWRITES++;
        solver.mzn_header += "constraint set_prop(" + toLoc(expr.base) + ", " + 
            toRep(expr.offset) + ", " + toTypRepLoc(expr.val) + ", " + 
            solver.NWRITES + ");\n";
        preProcess(expr.base);
        preProcess(expr.offset);
        preProcess(expr.val);
    }
    else if (expr instanceof DeleteField) {
        preProcess(expr.base);
        preProcess(expr.offset);
        preProcess(expr.val);
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

function fromTRL(expr, suff) {
    if (expr instanceof Constant) {
        if (suff == "TYP")
            return JSPrimitive[expr.getType()]
        else if (suff == "REP")
            return mznLiteral(expr.value)
        else
            return typeof(expr.value) === "object" ? expr.objectId + 1 : "0";
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
                    return suff + "S[get_prop_str(\"" + v + "\", " + 
                        toRep(expr.offset) + ", )]";
                case "number":
                    return suff + "S[get_num_prop(\"" + v + "\", " + 
                        toRep(expr.offset) + ", )]";
                case "boolean":
                    return suff + "S[get_bool_prop(\"" + v + "\", " +
                        toRep(expr.offset) + ", )]";
                default:
                    //FIXME: builtin objects, e.g. Math?
                    return suff + "S[get_prop(" + (expr.base.objectId + 1) + 
                        ", " + toRep(expr.offset) + ", )]";
            }
        }
        else if (expr.base instanceof PutField)
            return fromTRL(expr.base.val, suff);
        else return suff + "S[get_prop(" + toLoc(expr.base) + ", " + 
            toRep(expr.offset) + ")]";
    }
    else if (expr instanceof PutField)
        return fromTRL(expr.base, suff);
    else if (expr instanceof DeleteField) {
        console.log(expr)
        throw new Error("Unsupported: " + expr); //TODO
    }
    else if (expr instanceof Unary)
        return unaryOpToMZN(expr.op, expr.expr, suff);
    else if (expr instanceof Binary)
        return binaryOpToMZN(expr.op, expr.left, expr.right, suff);
    else if (expr.startsWith("to_num(") || 
             expr.startsWith("add(")    || expr.startsWith("sub(") || 
             expr.startsWith("mul(")    || expr.startsWith("divs("))
        return expr;  
    else
        throw new Error("Unsupported: " + expr);
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
    return tx === "Bool" || tx === "Boolean" ? rx
        : "to_bool(" + tx + ", " + rx + ")";
}
function toNum(x) {
    const tx = toTyp(x);
    const rx = toRep(x);
    return tx === "Num" || tx === "Number" ? rx 
        : "to_num(" + tx + ", " + rx + ")";
}
function toNum0(x) {
    const tx = toTyp(x);
    const rx = toRep(x);
    return tx === "Num" || tx === "Number" ? rx 
        : "to_num_0(" + tx + ", " + rx + ")";
}
 
function negate(x) {
  return x.startsWith("negate(") ? 
      x.slice(7, x.length - 1) : "negate(" + x + ")";
}

///// Unary /////

function unaryRelToMZN(op, arg) {
    switch (op) {
        case "!":
            if (arg instanceof Unary)
                return "not(" + unaryRelToMZN(arg.op, arg.expr) + ")";
            else if (arg instanceof Binary)
                return "not(" + binaryRelToMZN(arg.op, arg.left, arg.right) + ")";
            else
                return "not(" + toBool(arg) + ")";
        default:
            throw new Error("Unsupported unary: " + op);
    }
}

function unaryOpToMZN(op, arg, suff, solv) {
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
            return "divi(" + toNum(x) + ", " + toNum0(y) + ")";
        case "%":
            return "modu(" + toNum(x) + ", " + toNum(y) + ")";
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
            return "not abstract_eq(" + toTypRepLocs(left, right) + ")";
        case "!==":
            return "not strict_eq(" + toTypRepLocs(left, right) + ")";
        default:
            return arithBop(op, left, right) + " != \"0\"";
    }
}

exports.toMZNConstraint = toMZNConstraint; 
