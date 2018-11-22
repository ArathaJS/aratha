"use strict";

const sexpr = require("./sexpr");

class Constraint {
    constructor(value = true) {
        this.value = value;
    }

    negate() {
        this.value = !this.value;
    }

    toString() {
        return sexpr.stringify(this.toFormula());
    }
}

class BooleanConstraint extends Constraint {
    constructor(expr, value) {
        super(value);
        this.expr = expr;
    }

    isTrueIn(model) {
        try {
            return !!this.expr.eval(model) === this.value;
        } catch (e) {
            return false;
        }
    }

    toFormula() {
        const formula = this.expr.toBooleanFormula();
        return this.value ? formula : ["not", formula];
    }

    getId() {
        return sexpr.stringify(this.toFormula());
    }
}

exports.BooleanConstraint = BooleanConstraint;

const Type = require("./type");
const { SymbolicValue, PutField, Constant } = require("./symbolic");

const TYPE_MAP = {
    "undefined": Type.UNDEFINED,
    "null": Type.NULL,
    "number": Type.NUMBER,
    "string": Type.STRING,
    "boolean": Type.BOOLEAN,
    "object": Type.OBJECT
};

class TypeConstraint extends Constraint {
    constructor(type, subject, value) {
        super(value);
        this.type = type;
        if (subject instanceof PutField) {
            // We can only talk about types symbolic values of type Val, so we
            // need to get the base value, before any of our modifications.
            subject = subject.getTopBase();
        }

        this.subject = subject;
    }

    isTrueIn(model) {
        let val = this.subject;
        if (val instanceof SymbolicValue) {
            val = val.eval(model);
        }
        const typename = val === null ? "null" : typeof val;
        return this.type.has(TYPE_MAP[typename]) === this.value;
    }

    negate() {
        this.value = !this.value;
    }

    toFormula() {
        // If the type of the subject is known to fit into the constraint,
        // simplify it to just true or false.
        const constraintType = this.value ? this.type.types : Type.TOP & ~this.type.types;
        const subjectType = this.subject.getType();
        const intersection = constraintType & subjectType;
        if (intersection === subjectType) {
            return true;
        } else if (intersection === Type.BOTTOM) {
            return false;
        }

        // TODO: possible optimization: eliminate already known types?
        const formula = this.type.constraintFor(this.subject.toFormula());
        return this.value ? formula : ["not", formula];
    }

    getId() {
        return this.type.types.toString() + (this.subject.name || String(this.subject));
    }
}

exports.TypeConstraint = TypeConstraint;
