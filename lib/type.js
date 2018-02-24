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

        for (const k in predicates) {
            if (predicates.hasOwnProperty(k)) {
                if (!this.has(k)) {
                    negative.push(predicates[k]);
                }
            }
        }

        if (negative.length > 0) {
            const negativeFormula = _.map(negative, (x) => [x, value]);
            negativeFormula.unshift("or");
            return ["not", negativeFormula];
        } else {
            return "true";
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
