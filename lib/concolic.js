"use strict";

const _ = require("lodash");
const {Constant} = require("./symbolic");

class Concolic {
    constructor(concVal, symVal) {
        this.concVal = concVal;
        this.symVal = symVal;
    }
}

const SYMBOLIC = Symbol("SYMBOLIC");

exports.Concolic = Concolic;

function isConcolic(val) {
    return val instanceof Concolic || (_.isObject(val) && SYMBOLIC in val);
}
exports.isConcolic = isConcolic;

exports.concolizeObject = function(concVal) {
    if(!_.isObject(concVal))
        throw new Error("value must be an object");
    const symVal = new Constant(concVal);
    concVal[SYMBOLIC] = symVal;
    return symVal;
};

function getConcrete(val) {
    return val instanceof Concolic ? val.concVal : val;
}
exports.getConcrete = getConcrete;

function concretize(val) {
    val = getConcrete(val);
    if (_.isObject(val)) {
        const stack = [val];
        const seen = new Set(stack);
        while (stack.length > 0) {
            val = stack.pop();
            delete val[SYMBOLIC];
            for (const k in val) {
                // NOTE: Need to concretize every property, not just the own
                // ones. This could be slow if we examine many objects.
                const concVal = getConcrete(val[k]);
                try {
                    val[k] = concVal;
                } catch(e) {
                    // Swallow TypeErrors from trying to assign to non-writeable
                    // properties.
                }
                if (_.isObject(concVal) && !seen.has(concVal)) {
                    stack.push(concVal);
                    seen.add(concVal);
                }
            }
        }
    }
    return val;
}
exports.concretize = concretize;

exports.getSymbolic = function(val) {
    if (val instanceof Concolic) {
        return val.symVal;
    } else if (_.isObject(val) && SYMBOLIC in val) {
        return val[SYMBOLIC];
    } else {
        return new Constant(val);
    }
};

exports.setSymbolic = function(val, newSymVal) {
    if (val instanceof Concolic) {
        val.symVal = newSymVal;
    } else if (_.isObject(val)) {
        val[SYMBOLIC] = newSymVal;
    } else {
        throw new Error("can't set symbolic part of non-concolic value");
    }
};
