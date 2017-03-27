"use strict";

class Concolic {
    constructor(concVal, symVal) {
        this.concVal = concVal;
        this.symVal = symVal;
    }
}

exports.Concolic = Concolic;

exports.getConcrete = function(val) {
    return val instanceof Concolic ? val.concVal : val;
};

exports.getSymbolic = function(val) {
    return val instanceof Concolic ? val.symVal : val;
};
