"use strict";

const _ = require("lodash");

class Concolic {
    constructor(concVal, symVal) {
        this.concVal = concVal;
        this.symVal = symVal;
    }
}

const SYMBOLIC = Symbol("SYMBOLIC");

exports.Concolic = Concolic;

exports.isConcolic = function(val) {
    return val instanceof Concolic || (_.isObject(val) && SYMBOLIC in val);
};

exports.concolizeObject = function(concVal) {
    if(!_.isObject(concVal))
        throw new Error("value must be an object");
    const copy = _.clone(concVal);
    concVal[SYMBOLIC] = copy;
    return copy;
};

exports.getConcrete = function(val) {
    return val instanceof Concolic ? val.concVal : val;
};

exports.getSymbolic = function(val) {
    if (val instanceof Concolic) {
        return val.symVal;
    } else if (_.isObject(val)) {
        if (SYMBOLIC in val) {
            return val[SYMBOLIC];
        } else {
            // Return a snapshot of the object.
            return _.clone(val);
        }
    } else {
        return val;
    }
};

exports.setSymbolic = function(val, newSymVal) {
    if (val instanceof Concolic) {
        val.symVal = newSymVal;
    } else if (_.isObject(val) && SYMBOLIC in val) {
        val[SYMBOLIC] = newSymVal;
    } else {
        throw new Error("can't set symbolic part of non-concolic value");
    }
};
