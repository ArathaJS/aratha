const {
    Unary, Binary, Variable, Constant, GetField, PutField, DeleteField
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

var KNOWN_OBJECTS = new Set([]);

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
    if (expr instanceof Unary)
        mzn_cons += unaryRelToMZN(expr.op, expr.expr, solver);
    else if (expr instanceof Binary)
        mzn_cons += binaryRelToMZN(expr.op, expr.left, expr.right, solver);
    if (cons.value)
        return mzn_cons
    else
        return mzn_cons + ")";
}

function to_trl(x) {
  switch (typeof(x)) {
      case "null":
          return "Null, " + x + ", 0";
      case "undefined":
          return "Undef, " + x + ", 0";
      case "boolean":
          return "Bool, " + x + ", 0";
      case "number":
          return "Num, " + x + ", 0";
      case "string":
          return "Str, \"" + x + "\", 0";
      default:
          throw new Error("Unsupported: " + x);
  }
}

function toRep(expr, solver) {
    if (expr instanceof Constant)
        return '"' + expr.value + '"'
    else if (expr instanceof Variable)
        return "REP_" + expr.name
    else if (expr instanceof GetField) {
        if (expr.base instanceof Constant) {
            // Wrappers and constant objects.
            const v = expr.base.value;
            switch (typeof(v)) {
                case "string":
                    solver.NBUILTINS++;
                    return "REPS[get_prop_str(\"" + v + "\", " + 
                        toRep(expr.offset) + ")]";                
                case "number":
                    solver.NBUILTINS++;
                    return "REPS[get_num_prop(\"" + v + "\", " + 
                        toRep(expr.offset) + ")]";       
                case "boolean":
                    solver.NBUILTINS++;
                    return "REPS[get_bool_prop(\"" + v + "\", " + 
                        toRep(expr.offset) + ")]";
                default:
                    solver.NLOCS++;
                    const id = expr.base.objectId + 1;
                    if (!KNOWN_OBJECTS.has(id))
                        for (var key in expr.base.value) {
                            solver.NBUILTINS++;
                            solver.builtins += "constraint set_prop_const(" + id
                            + ", \"" + key + "\", " + to_trl(expr.base.value[key]) 
                            + ", " + solver.NBUILTINS + ");\n";                             
                        }
                    return "REPS[get_prop(" + id + ", " + toRep(expr.offset) + ")]"; //FIXME: builtin objects, e.g. Math?
            }
        }
        if (expr.offset instanceof Constant) {
            // Built-in properties, including index access.
            const v = expr.offset.value;
            solver.NBUILTINS++;
            solver.NLOCS++;
            if (BUILTIN_PROPS.has(v))
                solver.builtins += "constraint set_builtin_prop(" 
                    + toLoc(expr.base) + ", \"" + v + "\", " + toTyp(expr.base)+ 
                    ", " + toRep(expr.base) + ", " + solver.NBUILTINS + ");\n";
            else if (isIndex(v))
                solver.builtins += "constraint set_access_builtin(" 
                    + toLoc(expr.base) + ", \"" + v + "\", " + toTyp(expr.base)+ 
                    ", " + toRep(expr.base) + ", " + solver.NBUILTINS + ");\n";
        }
        else {
            const type = new Type(expr.offset.type);
            if (type.has(Type.BOOLEAN)) {
                solver.builtins += "constraint set_bool_builtins(" 
                    + toLoc(expr.base) + ", " + toTyp(expr.base) + ", " 
                    + toRep(expr.base) + ", " + (solver.NBUILTINS + 1) + ");\n";
                solver.NBUILTINS += BOOL_BUILTINS;
            }
            if (type.has(Type.NUMBER)) {
                solver.builtins += "constraint set_num_builtins(" 
                    + toLoc(expr.base) + ", " + toTyp(expr.base) + ", " 
                    + toRep(expr.base) + ", " + (solver.NBUILTINS + 1) + ");\n";
                solver.NBUILTINS += NUM_BUILTINS;
            }
            if (type.has(Type.STRING)) {
                solver.builtins += "constraint set_str_builtins(" 
                    + toLoc(expr.base) + ", " + toTyp(expr.base) + ", " 
                    + toRep(expr.base) + ", " + (solver.NBUILTINS + 1) + ");\n";
                solver.NBUILTINS += STR_BUILTINS;
            }            
        }
        return "REPS[get_prop(" + toLoc(expr.base) + ", " + 
                    toRep(expr.offset) + ")]";
    }
    else if (expr instanceof PutField) {
        console.log(expr)
        throw new Error("Unsupported PutField");
        //solver.NWRITES++;
        return undefined;
    }
    else if (expr instanceof DeleteField) {
        console.log(expr)
        throw new Error("Unsupported DeleteField");
        //solver.NWRITES++;
        return undefined;
    }
    else if (expr instanceof Unary)
        return unaryOpToMZN(expr.op, expr.expr, "REP", solver);
    else if (expr instanceof Binary)
        return binaryOpToMZN(expr.op, expr.left, expr.right, "REP", solver);
    else if (expr.startsWith("to_num(") || 
             expr.startsWith("add(")   || expr.startsWith("sub(") || 
             expr.startsWith("mul(")   || expr.startsWith("divs("))
        return expr;  
    else
        throw new Error("Unsupported: " + expr);
}

function toTyp(expr) {
    if (expr instanceof Constant)
        return JSPrimitive[expr.getType()]
    else if (expr instanceof Variable)
        return "TYP_" + expr.name
    else if (expr instanceof GetField) {
        if (expr.base instanceof Constant) {
            const v = expr.base.value;
            switch (typeof(v)) {
                case "string":
                    return "TYPS[get_prop_str(\"" + v + "\", " + 
                       toRep(expr.offset) + ")]";
                case "object":
                    return "TYPS[get_prop(" + 
                        toLoc(expr.base) + ", " + toRep(expr.offset) + ")]"
            }
        }
        else
            return "TYPS[get_prop(" + 
                toLoc(expr.base) + ", " + toRep(expr.offset) + ")]"
    }
    else if (expr instanceof PutField) {
        throw new Error("Unsupported PutField");
    }
    else if (expr instanceof Unary)
        return unaryOpToMZN(expr.op, expr.expr, "TYP");
    else if (expr instanceof Binary)
        return binaryOpToMZN(expr.op, expr.left, expr.right, "TYP");
    else if (expr.startsWith("to_num(") || 
             expr.startsWith("add(")   || expr.startsWith("sub(") || 
             expr.startsWith("mul(")   || expr.startsWith("divs("))
        return "Num";
    else
        throw new Error("Unsupported: " + expr);
}

function toLoc(expr) {
    if (expr instanceof Constant) {
        if (typeof(expr.value) === "object")
            return expr.objectId + 1
        else
            return "0";
    }
    else if (expr instanceof Variable)
        return "LOC_" + expr.name
    else if (expr instanceof GetField) {
        if (expr.base instanceof Constant) {
            const v = expr.base.value;
            switch (typeof(v)) {
                case "string":
                    return "LOCS[get_prop_str(\"" + v + "\", " + 
                        toRep(expr.offset) + ")]";
                case "object":
                    return "REFS[get_prop(" + 
                        toLoc(expr.base) + ", " + toRep(expr.offset) + ")]";
           }
        }
        else
            return "REFS[get_prop(" + 
                toLoc(expr.base) + ", " + toRep(expr.offset) + ")]";
    }
    else if (expr instanceof PutField) {
       throw new Error("Unsupported PutField");
    }
    else if (expr instanceof Unary)
        return unaryOpToMZN(expr.op, expr.expr, "LOC");
    else if (expr instanceof Binary)
        return binaryOpToMZN(expr.op, expr.left, expr.right, "LOC");         
    else
        throw new Error("Unsupported: " + expr);
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
        case "LOC": {
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

function toTyps(x, y) {
    return toTyp(x)  + ", "  + toTyp(y)
}
function toTypRep(x, s) {
    return toTyp(x)  + ", "  + toRep(x, s)
}
function toTypReps(x, y, s) {
    return toTypRep(x, s) + ", "  + toTypRep(y, s)
}
function toTypRepLoc(x, s) {
    return toTyp(x)  + ", "  + toRep(x, s)  + ", " + toLoc(x);
}
function toTypRepLocs(x, y, s) {
    return toTypRepLoc(x, s)  + ", "  + toTypRepLoc(y, s);
}

function toBool(x, s) {
    const tx = toTyp(x);
    const rx = toRep(x, s);
    return tx === "Bool" || tx === "Boolean" ?
        rx : "to_bool(" + tx + ", " + rx + ")";
}
function toNum(x, s) {
    const tx = toTyp(x);
    const rx = toRep(x, s);
    return tx === "Num" || tx === "Number" ? 
        rx : "to_num(" + tx + ", " + rx + ")";
}
function toNum0(x, s) {
    const tx = toTyp(x);
    const rx = toRep(x, s);
    return tx === "Num" || tx === "Number" ?
        rx : "to_num_0(" + tx + ", " + rx + ")";
}
 
function negate(x) {
  return x.startsWith("negate(") ? 
      x.slice(7, x.length - 1) : "negate(" + toNum(x) + ")";
}
      
function arithBop(op, x, y, s) {
    switch (op) {
        case "+":
            return "plus_REP(" + toTypReps(x, y, s) + ")";
        case "-":
            return "sub(" + toNum(x, s) + ", " + toNum(y, s) + ")";
        case "*":
            return "mul(" + toNum(x, s) + ", " + toNum(y, s) + ")";
        case "/":
            return "divs(" + toNum(x, s) + ", " + toNum0(y, s) + ")";
    }
}

function binaryOpToMZN(op, left, right, suff, solv) {
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
                    return "Num";
            }
        }
        case "REP": {
            switch (op) {
                case "+":
                case "-":
                case "*":
                case "/":
                    return arithBop(op, left, right, solv);
            }
        }
        case "LOC": {
            switch (op) {
                case "+":
                case "-":
                case "*":
                case "/":
                    return "0"
            }
        }
    }
    throw new Error("Unsupported binary: " + op);
}

function unaryRelToMZN(op, arg, solv) {
    switch (op) {
        case "!":
            if (arg instanceof Unary)
                return "not(" + unaryRelToMZN(arg.op, arg.expr, solv) + ")";
            else if (arg instanceof Binary)
                return "not(" + binaryRelToMZN(arg.op, arg.left, arg.right, solv) + ")";
            else
                return "not(" + toBool(arg, solv) + ")";
        default:
            throw new Error("Unsupported unary: " + op);
    }
}

function binaryRelToMZN(op, left, right, solv) {
    switch (op) {
        case "<":
            return "lt(" + toTypReps(left, right, solv) + ")";
        case "<=":
            return "le(" + toTypReps(left, right, solv) + ")";
        case ">":
            return "lt(" + toTypReps(right, left, solv) + ")";
        case ">=":
            return "le(" + toTypReps(right, left, solv) + ")";
        case "==":
            return "abstract_eq(" + toTypRepLocs(left, right, solv) + ")";
        case "===":
            return "strict_eq(" + toTypRepLocs(left, right, solv) + ")";
        case "!=":
            return "not abstract_eq(" + toTypRepLocs(left, right, solv) + ")";
        case "!==":
            return "not strict_eq(" + toTypRepLocs(left, right, solv) + ")";
        default:
            throw new Error("Unsupported binary: " + op);
    }
}

exports.toMZNConstraint = toMZNConstraint; 
