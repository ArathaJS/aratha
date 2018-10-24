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
            formula.unshift("or");
            return formula;
        } else {
            const negativeFormula = _.map(negative, (x) => [x, value]);
            negativeFormula.unshift("or");
            return ["not", negativeFormula];
        }
    }

    valueConforms(value) {
        switch (typeof value) {
            case "undefined":
                return this.has(Type.UNDEFINED);
            case "boolean":
                return this.has(Type.BOOLEAN);
            case "string":
                return this.has(Type.STRING);
            case "number":
                return this.has(Type.NUMBER);
            case "object":
                return value === null ? this.has(Type.NULL) : this.has(Type.OBJECT);
            case "function":
                return this.has(Type.OBJECT);
            default:
                throw new Error("cannot check type of host object " + value);
        }
    }
    
    toJSType() {
        var jstype = "{";
        if (this.has(Type.NULL))
            jstype += "Null, ";
        if (this.has(Type.UNDEFINED))
            jstype += "Undef, ";
        if (this.has(Type.BOOLEAN))
            jstype += "Bool, ";
        if (this.has(Type.NUMBER))
            jstype += "Num, ";    
        if (this.has(Type.STRING))        
            jstype += "Str, ";        
        if (this.has(Type.OBJECT)) //FIXME: Only deal few objects atm.
            jstype += "Object, Array, Function";
        return jstype + "}";    
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
