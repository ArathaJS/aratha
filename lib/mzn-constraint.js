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
//              console.log(solver.builtins);
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
//                solver.NLOCS++;
                solver.builtins += "constraint set_bool_builtins(" 
                    + toTyp(expr.base) + ", " + toRep(expr.base)  + ", "
                    + toLoc(expr.base) + ", " + (solver.NBUILTINS + 1) + ");\n";
                solver.NBUILTINS += BOOL_BUILTINS;
            }
            if (type.has(Type.NUMBER)) {
//                solver.NLOCS++;
                solver.builtins += "constraint set_num_builtins(" 
                    + toTyp(expr.base) + ", " + toRep(expr.base)  + ", "
                    + toLoc(expr.base) + ", " + (solver.NBUILTINS + 1) + ");\n";
                solver.NBUILTINS += NUM_BUILTINS;
            }
            if (type.has(Type.STRING)) {
//                solver.NLOCS++;
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
    else
        console.log("Unsupported:", expr);
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
    else
        console.log("Unsupported:", expr);
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
    else
        console.log("Unsupported:", expr);
}

function unaryOpToMZN(op, arg, suff, solv) {
    const x = toTyp(arg)  + ", "  + toRep(arg, solv)  + ", " + toLoc(arg);
    switch (op) {
        case "typeof":
            return "typeof_" + suff + "(" + x + ")";
        case "-":
            return "u_minus_" + suff + "(" + x + ")";
        case "+":
            return "u_plus_" + suff + "(" + x + ")";
        default:
            console.log("Unsupported unary:", op, arg, suff);
    }
}

function binaryRelToMZN(op, left, right, solv) {
    const lhs = toTyp(left)  + ", "  + toRep(left, solv)  + ", " + toLoc(left);
    const rhs = toTyp(right) + ", "  + toRep(right, solv) + ", " + toLoc(right);
    switch (op) {
        case "<":
            return "lt(" + lhs + ", " + rhs + ")";
        case "<=":
            return "le(" + lhs + ", " + rhs + ")";
        case ">":
            return "gt(" + lhs + ", " + rhs + ")";        
        case ">=":
            return "ge(" + lhs + ", " + rhs + ")";
        case "==":
            return "abstract_eq(" + lhs + ", " + rhs + ")";
        case "===":
            return "strict_eq(" + lhs + ", " + rhs + ")";
        case "!=":
            return "not abstract_eq(" + lhs + ", " + rhs + ")";
        case "!==":
            return "not strict_eq(" + lhs + ", " + rhs + ")";
        default:
            console.log("Unsupported binary:", op, left, right);
    }
}

exports.toMZNConstraint = toMZNConstraint; 
