const {
    Binary, Variable, Constant, GetField
} = require("./symbolic");

const JSPrimitive = {
    1: "Undef",
    2: "Null",
    4: "Bool",
    8: "Str",
    16: "Num",
};

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
    console.log(mzn_cons);
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
            if (typeof(v) === "string") {
                this.NUM_WRITES += 1;
                return "REPS[get_string_prop(\"" + v + "\", " + 
                    toRep(expr.offset) + ")]";                
            }
        }
        if (expr.offset instanceof Constant
        && BUILTIN_PROPS.has(expr.offset.value)) {
            solver.NUM_BUILTIN++;
            solver.builtins += "constraint set_builtin_prop(" 
                + toTyp(expr.base) + ", " + toRep(expr.base)  + ", "
                + toLoc(expr.base) + ", \"" + expr.offset.value + "\", "
                + solver.NUM_BUILTIN + ");\n";
//            console.log(solver.builtins);
        }        
        return "REPS[get_prop(" + toLoc(expr.base) + ", " + 
            toRep(expr.offset) + ")]";
    }
    else if (expr instanceof PutField) {
        solver.NUM_WRITES++;
        return undefined;
    }
    else if (expr instanceof DeleteField) {
        solver.NUM_WRITES++;
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
                this.NUM_WRITES += 1;
                return "TYPS[get_string_prop(\"" + v + "\", " + 
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
                this.NUM_WRITES += 1;
                return "LOCS[get_string_prop(\"" + v + "\", " + 
                    toRep(expr.offset) + ")]";                
            }
        }
        else
            return "REFS[get_prop(" + 
                toLoc(expr.base) + ", " + toRep(expr.offset) + ")]";
}

function binaryToMZN(op, left, right, solv) {
    const lhs = toTyp(left)  + ", "  + toRep(left, solv)  + ", " + toLoc(left);
    const rhs = toTyp(right) + ", "  + toRep(right, solv) + ", " + toLoc(right);
    switch (op) {
        case "<":
            return "lt(" + lhs + ", " + rhs + ")";
        case "===":
            return "strict_eq(" + lhs + ", " + rhs + ")";
    }
}

exports.toMZNConstraint = toMZNConstraint; 
