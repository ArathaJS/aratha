"use strict";

class Constraint {
    constructor(expr, value) {
        this.expr = expr;
        this.value = value;
    }

    negate() {
        this.value = !this.value;
    }

    toFormula() {
        const formula = this.expr.toFormula();
        return this.value ? formula : ["not", formula];
    }
}

module.exports = Constraint;
