"use strict";

const _ = require("lodash");

const predicates = {
    1: "is-undefined",
    2: "is-null",
    4: "is-Boolean",
    8: "is-Str",
    16: "is-Num",
    32: "is-Obj"
};

class Type {
    constructor(types) {
        if (types === undefined) {
            types = Type.TOP;
        }

        this.types = types & Type.TOP;
    }

    requireTypes(types) { this.types &= types; }
    forbidTypes(types) { this.types &= ~types; }

    intersection(type) { return new Type(this.types & type.types); }

    valid() { return this.types !== Type.BOTTOM; }
    trivial() { return this.types === Type.TOP; }

    has(types) { return (this.types & types) !== Type.BOTTOM; }

    isSingleton() {
        return this.types in predicates;
    }

    isEqual(other) {
        return this.types === other.types;
    }

    constraintFor(value) {
        const negative = [];
        const positive = [];

        for (const k in predicates) {
            if (predicates.hasOwnProperty(k)) {
                if (this.has(k)) {
                    positive.push(predicates[k]);
                } else {
                    negative.push(predicates[k]);
                }
            }
        }

        if (positive.length === 0)
            return false;

        if (negative.length === 0)
            return true;

        if (positive.length === 1) {
            return [positive[0], value];
        }

        if (negative.length === 1) {
            return ["not", [negative[0], value]];
        }

        if (positive.length <= negative.length) {
            const formula = _.map(positive, (x) => [x, value]);
            formula.unshift("and");
            return formula;
        } else {
            const negativeFormula = _.map(negative, (x) => [x, value]);
            negativeFormula.unshift("or");
            return ["not", negativeFormula];
        }
    }
}

Type.UNDEFINED = 1;
Type.NULL = 1 << 1;
Type.BOOLEAN = 1 << 2;
Type.STRING = 1 << 3;
Type.NUMBER = 1 << 4;
Type.OBJECT = 1 << 5;

Type.TOP = ~(~0 << 6);
Type.BOTTOM = 0;

module.exports = Type;
