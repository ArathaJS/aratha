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

exports.isConcolic = function(val) {
    return val instanceof Concolic || (_.isObject(val) && SYMBOLIC in val);
};

exports.concolizeObject = function(concVal) {
    if(!_.isObject(concVal))
        throw new Error("value must be an object");
    const symVal = new Constant(concVal);
    concVal[SYMBOLIC] = symVal;
    return symVal;
};

exports.getConcrete = function(val) {
    return val instanceof Concolic ? val.concVal : val;
};

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
