const {
    Binary, Variable, Constant, GetField
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
const STR_BUILTINS  = 1;

//TODO: Add more built-in properties. 
const BUILTIN_PROPS = new Set([
  "length", "__proto__", "constructor", 
])

function toMZNConstraint(cons, solver) {
    var mzn_cons = "% SMT constraint: " + cons + "\nconstraint "
    if (!cons.value)
        mzn_cons += "not (";
    const expr = cons.expr
    if (cons.expr instanceof Binary)
        mzn_cons += binaryToMZN(expr.op, expr.left, expr.right, solver);
    if (!cons.value)
        mzn_cons += ")";
    return mzn_cons;
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
            if (BUILTIN_PROPS.has(expr.offset.value)) {
                solver.NBUILTINS++;
                solver.NLOCS++;
                solver.builtins += "constraint set_builtin_prop(" 
                    + toTyp(expr.base) + ", " + toRep(expr.base)  + ", "
                    + toLoc(expr.base) + ", \"" + expr.offset.value + "\", "
                    + solver.NBUILTINS + ");\n";
//              console.log(solver.builtins);
            }
        }
        else {
            const type = new Type(expr.offset.type);
            if (type.has(Type.BOOLEAN)) {
                solver.NLOCS++;
                solver.builtins += "constraint set_bool_builtins(" 
                    + toTyp(expr.base) + ", " + toRep(expr.base)  + ", "
                    + toLoc(expr.base) + ", " + (solver.NBUILTINS + 1) + ");\n";
                solver.NBUILTINS += BOOL_BUILTINS;
            }
            if (type.has(Type.NUMBER)) {
                solver.NLOCS++;
                solver.builtins += "constraint set_num_builtins(" 
                    + toTyp(expr.base) + ", " + toRep(expr.base)  + ", "
                    + toLoc(expr.base) + ", " + (solver.NBUILTINS + 1) + ");\n";
                solver.NBUILTINS += NUM_BUILTINS;
            }
            if (type.has(Type.STRING)) {
                solver.NLOCS++;
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
}

function binaryToMZN(op, left, right, solv) {
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
        case "===":
            return "strict_eq(" + lhs + ", " + rhs + ")";
    }
}

exports.toMZNConstraint = toMZNConstraint; 
