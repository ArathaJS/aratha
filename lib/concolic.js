"use strict";

const _ = require("lodash");
const { Constant } = require("./symbolic");

class Concolic {
    constructor(concVal, symVal) {
        this.concVal = concVal;
        this.symVal = symVal;
    }
}

const SYMBOLIC = Symbol("SYMBOLIC");

exports.Concolic = Concolic;

const HOP = Object.prototype.hasOwnProperty;

function isConcolic(val) {
    return val instanceof Concolic || (_.isObject(val) && HOP.call(val, SYMBOLIC));
}
exports.isConcolic = isConcolic;

exports.concolizeObject = function(concVal) {
    if (!_.isObject(concVal))
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
    // throw new Error(val);
    val = getConcrete(val);
    if (_.isObject(val)) {
        const stack = [val];
        const seen = new Set(stack);
        while (stack.length > 0) {
            const obj = stack.pop();
            if (!_.isObject(obj))
                continue;

            delete val[SYMBOLIC];
            let entries;
            try {
                entries = Object.entries(obj);
            } catch (e) {
                // BUG: Node.js's TTY object (on Windows, at least) throws an
                // error if you try to use Object.entries() on it. As such, this
                // needs to be wrapped in order to swallow that error.
                entries = [];
            }

            for (const [k, v] of entries) {
                // NOTE: Need to concretize every property, not just the own
                // ones. This could be slow if we examine many objects.
                const concVal = getConcrete(v);
                try {
                    val[k] = concVal;
                } catch (e) {
                    // Swallow TypeErrors from trying to assign to non-writeable
                    // properties.
                }
                if (_.isObject(concVal) && !seen.has(concVal)) {
                    stack.push(concVal);
                    seen.add(concVal);
                }
            }

            const proto = Object.getPrototypeOf(obj);
            if (_.isObject(proto) && !seen.has(proto)) {
                stack.push(proto);
                seen.add(proto);
            }
        }
    }
    return val;
}
exports.concretize = concretize;

function shallowConcretize(val) {
    // throw new Error(val);
    val = getConcrete(val);
    if (_.isObject(val)) {
        for (const [k, v] of Object.entries(val)) {
            if (isConcolic(v)) {
                try {
                    val[k] = getConcrete(v);
                } catch (e) {
                    // Swallow TypeErrors from trying to assign to non-writeable
                    // properties.
                }
            }
        }
    }
    return val;
}
exports.shallowConcretize = shallowConcretize;

exports.getSymbolic = function(val) {
    let result;
    if (val instanceof Concolic) {
        result = val.symVal;
    } else if (_.isObject(val) && SYMBOLIC in val) {
        result = val[SYMBOLIC];
    } else {
        return new Constant(val);
    }

    return result.forcedConstant ? result.forcedConstant : result;
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
