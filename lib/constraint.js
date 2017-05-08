"use strict";

class Constraint {
    constructor(expr, value) {
        this.expr = expr;
        this.value = value;
    }

    negate() {
        this.value = !this.value;
    }

    isTrueIn(model) {
        return this.expr.eval(model) === this.value;
    }

    toFormula() {
        const formula = this.expr.toFormula();
        return this.value ? formula : ["not", formula];
    }

    getId() { return String(this.expr); }

    toString() { return this.toFormula().toString(); }
}

module.exports = Constraint;
