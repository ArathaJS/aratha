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
    var mzn_cons = "% SMT constraint: " + cons + "\nconstraint "
    if (!cons.value)
        mzn_cons += "not (";
    const expr = cons.expr;
    if (expr instanceof Unary)
        mzn_cons += unaryOpToMZN(expr.op, expr.expr, solver);
    else if (expr instanceof Binary)
        mzn_cons += binaryRelToMZN(expr.op, expr.left, expr.right, solver);
    if (cons.value)
        return mzn_cons
    else
        return mzn_cons + ")";
}

function toRep(expr, solver) {
    if (expr instanceof Constant)
        return '"' + expr.value + '"'
    else if (expr instanceof Variable)
        return "REP_" + expr.name
    else if (expr instanceof GetField) {
        if (expr.base instanceof Constant) {
            const v = expr.base.value;
            switch (typeof(v)) {
                case "string":
                    solver.NWRITES += 1;
                    return "REPS[get_str_prop(\"" + v + "\", " + 
                        toRep(expr.offset) + ")]";                
                case "number":
                    solver.NWRITES += 1;
                    return "REPS[get_num_prop(\"" + v + "\", " + 
                        toRep(expr.offset) + ")]";       
                case "boolean":
                    solver.NWRITES += 1;
                    return "REPS[get_bool_prop(\"" + v + "\", " + 
                        toRep(expr.offset) + ")]";       
            }
        }
        if (expr.offset instanceof Constant) {
            const v = expr.offset.value;
            if (BUILTIN_PROPS.has(v)) {
                solver.NBUILTINS++;
                solver.NLOCS++;
                solver.builtins += "constraint set_builtin_prop(" 
                    + toTyp(expr.base) + ", " + toRep(expr.base)  + ", "
                    + toLoc(expr.base) + ", \"" + v + "\", "
                    + solver.NBUILTINS + ");\n";
            }
            else if (isIndex(v)) {
                solver.NBUILTINS++;
                solver.NLOCS++;
                solver.builtins += "constraint set_access_prop(" 
                    + toTyp(expr.base) + ", " + toRep(expr.base)  + ", "
                    + toLoc(expr.base) + ", \"" + v + "\", "
                    + solver.NBUILTINS + ");\n";
            }
        }
        else {
            const type = new Type(expr.offset.type);
            if (type.has(Type.BOOLEAN)) {
                solver.builtins += "constraint set_bool_builtins(" 
                    + toTyp(expr.base) + ", " + toRep(expr.base)  + ", "
                    + toLoc(expr.base) + ", " + (solver.NBUILTINS + 1) + ");\n";
                solver.NBUILTINS += BOOL_BUILTINS;
            }
            if (type.has(Type.NUMBER)) {
                solver.builtins += "constraint set_num_builtins(" 
                    + toTyp(expr.base) + ", " + toRep(expr.base)  + ", "
                    + toLoc(expr.base) + ", " + (solver.NBUILTINS + 1) + ");\n";
                solver.NBUILTINS += NUM_BUILTINS;
            }
            if (type.has(Type.STRING)) {
                solver.builtins += "constraint set_str_builtins(" 
                    + toTyp(expr.base) + ", " + toRep(expr.base)  + ", "
                    + toLoc(expr.base) + ", " + (solver.NBUILTINS + 1) + ");\n";
                solver.NBUILTINS += STR_BUILTINS;
            }            
        }
        return "REPS[get_prop(" + toLoc(expr.base) + ", " + 
                    toRep(expr.offset) + ")]";
    }
    else if (expr instanceof PutField) {
        solver.NWRITES++;
        return undefined;
    }
    else if (expr instanceof DeleteField) {
        solver.NWRITES++;
        return undefined;
    }
    else if (expr instanceof Unary)
        return unaryOpToMZN(expr.op, expr.expr, "REP", solver);
    else if (expr instanceof Binary)
        return binaryOpToMZN(expr.op, expr.left, expr.right, "REP", solver);         
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
            if (typeof(v) === "string") {
                return "TYPS[get_str_prop(\"" + v + "\", " + 
                    toRep(expr.offset) + ")]";                
            }
        }
        else
            return "TYPS[get_prop(" + 
                toLoc(expr.base) + ", " + toRep(expr.offset) + ")]"
    }
//    else if (expr instanceof PutField) {
//        
//    }
    else if (expr instanceof Unary)
        return unaryOpToMZN(expr.op, expr.expr, "TYP");
    else if (expr instanceof Binary)
        return binaryOpToMZN(expr.op, expr.left, expr.right, "TYP");
    else
        throw new Error("Unsupported: " + expr);
}

function toLoc(expr) {
    if (expr instanceof Constant)
        return "0";
    else if (expr instanceof Variable)
        return "LOC_" + expr.name
    else if (expr instanceof GetField)
        if (expr.base instanceof Constant) {
            const v = expr.base.value;
            if (typeof(v) === "string") {
                return "LOCS[get_str_prop(\"" + v + "\", " + 
                    toRep(expr.offset) + ")]";                
            }
        }
        else {
            return "REFS[get_prop(" + 
                toLoc(expr.base) + ", " + toRep(expr.offset) + ")]";}
//    else if (expr instanceof PutField) {
//       
//    }
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
            }
        }    
        case "REP": {
            switch (op) {
                case "typeof":
                    return "typeof_REP(" + toTyp(arg) + ")";
                case "+":
                    return toNum(arg);
                case "-":
                    return "negate(" + toNum(arg) + ")";
            }
        }
        case "LOC": {
            switch (op) {
                case "typeof":
                case "+":
                case "-":
                    return "0"
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

function toNum(x, s) {
    const tx = toTyp(x);
    const rx = toRep(x, s);
    if (tx === "Num")
        return rx;
    else
        return "to_num(" + tx + ", " + rx + ")";
}
 
function arithBop(op, x, y, s) {
    switch (op) {
        case "+":
            return "plus_REP(" + toTypReps(x, y, s) + ")";
        case "-":
            return "add_REP(" + toNum(x, s) + ", negate(" + toNum(y, s) + "))";
        case "*":
            return "mul_REP(" + toNum(x, s) + ", negate(" + toNum(y, s) + "))";
        case "/":
            return "div_REP(" + toNum(x, s) + ", negate(" + toNum(y, s) + "))";
    }
}

function binaryOpToMZN(op, left, right, suff, solv) {
    switch (suff) {
        case "TYP": {
            switch (op) {
                case "+":
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
