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

exports.concolizeObject = function(concVal, symVal) {
    if(!_.isObject(concVal))
        throw new Error("value must be an object");
    concVal[SYMBOLIC] = symVal;
    return symVal;
};

exports.getConcrete = function(val) {
    return val instanceof Concolic ? val.concVal : val;
};

exports.getSymbolic = function(val) {
    return val instanceof Concolic ? val.symVal : (_.isObject(val) && SYMBOLIC in val ? val[SYMBOLIC] : val);
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
