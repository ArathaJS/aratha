"use strict";

const _ = require("lodash");

const {
    StringToString,
    StringConcat,
    StringCharAt,
    StringSubstr,
    StringSubstring,
    StringSlice,
    StringIndexOf,
    StringSearch,
    StringReplace,
    RegExpTest,
    NewArray,
    NewBoolean,
    ToBoolean,
    NewNumber,
    ToNumber,
    NewObject,
    ToObject,
    NewString,
    ToString,
    NewRegExp,
    ParseInt
} = require("./symbolic");
const {
    Concolic,
    isConcolic,
    getConcrete,
    getSymbolic,
    shallowConcretize
} = require("./concolic");

const callModels = new Map();

// From clause 15 "Standard Built-in ECMAScript Objects" of the ECMAScript 5
// standard:
//
// "None of the built-in functions described in this clause that are not
// constructors shall implement the [[Construct]] internal method unless
// otherwise specified in the description of a particular function. None of the
// built-in functions described in this clause shall have a prototype property
// unless otherwise specified in the description of a particular function."

function setCallModel(concreteFn, symbolicFn, concretizer = getConcrete) {
    if (!symbolicFn) {
        callModels.set(concreteFn, null);
        return;
    }

    const shim = function(...args) {
        const cbase = concretizer(this),
            sbase = getSymbolic(this);
        const cargs = _.map(args, concretizer),
            sargs = _.map(args, getSymbolic);

        return new Concolic(concreteFn.apply(cbase, cargs), new symbolicFn(sbase, ...sargs));
    };
    callModels.set(concreteFn, shim);
}

// String built-in function models

setCallModel(String.prototype.toString, StringToString);
setCallModel(String.prototype.valueOf, StringToString);
setCallModel(String.prototype.charAt, StringCharAt);
setCallModel(String.prototype.substring, StringSubstring);
setCallModel(String.prototype.substr, StringSubstr);
setCallModel(String.prototype.slice, StringSlice);
setCallModel(String.prototype.indexOf, StringIndexOf);
setCallModel(String.prototype.search, StringSearch);
setCallModel(String.prototype.replace, StringReplace);
setCallModel(String.prototype.concat, StringConcat);

// Unimplemented models
setCallModel(String.prototype.split);
setCallModel(String.prototype.charCodeAt);
setCallModel(String.prototype.match);

callModels.set(String.prototype.search, function(searchValue) {
    const csearchValue = getConcrete(searchValue);
    const cresult = String.prototype.search.call(getConcrete(this), csearchValue);
    // If the search value is a RegExp, only return the concrete result.
    // Otherwise, it's a string, and we can use our StringSearch model to return
    // a concolic value.
    if (_.isRegExp(csearchValue)) {
        return cresult;
    } else {
        return new Concolic(cresult, new StringSearch(getSymbolic(this), getSymbolic(searchValue)));
    }
});

callModels.set(String.prototype.replace, function(searchValue, replaceValue) {
    const csearchValue = getConcrete(searchValue);
    const creplaceValue = getConcrete(replaceValue);
    const cresult = String.prototype.replace.call(getConcrete(this), csearchValue, creplaceValue);
    if (_.isRegExp(csearchValue) || _.isFunction(creplaceValue)) {
        return cresult;
    } else {
        return new Concolic(cresult, new StringReplace(getSymbolic(this), getSymbolic(searchValue), getSymbolic(replaceValue)));
    }
});

callModels.set(String.prototype.trim, function() {
    const cbase = getConcrete(this);
    const cresult = String.prototype.trim.call(cbase);
    if (cbase === cresult) {
        return this;
    } else {
        return cresult;
    }
});

// RegExp built-in function models

setCallModel(RegExp.prototype.test, RegExpTest);

// Number built-in function models

// Implementation of ECMAScript's ToInteger operation.

function sign(value) {
    return value / Math.abs(value);
}

function toInteger(value) {
    value = Number(value);

    // ToInteger(NaN) = +0
    if (value !== value)
        return +0;

    if (!isFinite(value) || value === 0)
        return value;

    return sign(value) * Math.floor(Math.abs(value));
}

callModels.set(Number.prototype.toString, function(...args) {
    const cbase = getConcrete(this),
        sbase = getSymbolic(this),
        cargs = _.map(args, getConcrete);
    // TODO: finish this model. Number.prototype.toString() optionally takes a
    // radix between 2 and 36 (defaults to 10). It also throws a TypeError if
    // its base is not a Number or a Number object. The conversion algorithm is
    // implementation-dependent for radixes other than 10, but the standard says
    // it should be a generalization of the ToString() algorithm for Numbers.
    // Lowercase letters a-z are used for digits 10-35.
    if (args.length > 0) {
        // If a radix was given, it must be 10 to avoid concretizing the
        // operation, as the solver-side str.to.int and int.to.str functions
        // only operate in base 10.
        //
        // NOTE: is it safe to not concretize when the radix is concolic, but
        // its concrete value is 10?
        const radix = args[0];
        if (toInteger(getConcrete(radix)) !== 10) {
            return Number.prototype.toString.apply(cbase, cargs);
        }
    }
    return new Concolic(Number.prototype.toString.apply(cbase, cargs), new ToString(sbase));
});

function toInt32(value) {
    value = Number(value);
    if (!isFinite(value) || value === 0)
        return +0;
    value = (sign(value) * Math.floor(Math.abs(value))) % 2**32;
    return value >= 2**31 ? value - 2**31 : value;
}

callModels.set(parseInt, function(...args) {
    const cbase = getConcrete(this);
    const cargs = _.map(args, getConcrete);

    if (args.length > 1) {
        const radix = args[1];
        if (toInt32(getConcrete(radix)) === 10) {
            return new Concolic(parseInt.apply(cbase, cargs), new ParseInt(getSymbolic(args[0]), getSymbolic(radix)));
        }
        console.warn("concretizing call to parseInt: received non-decimal radix", radix);
    } else {
        console.warn("concretizing call to parseInt: did not receive radix");
    }

    return parseInt.apply(cbase, cargs);
});

// Array built-in function models

function overrideConcBasePassArgs(concreteFn) {
    callModels.set(concreteFn, function(...args) {
        const base = isConcolic(this) ? shallowConcretize(this) : this;
        return concreteFn.apply(base, args);
    });
}

overrideConcBasePassArgs(Array.prototype.shift);
overrideConcBasePassArgs(Array.prototype.unshift);
overrideConcBasePassArgs(Array.prototype.push);
overrideConcBasePassArgs(Array.prototype.filter);
overrideConcBasePassArgs(Array.prototype.join);

// Math function models

setCallModel(Math.sin);
setCallModel(Math.cos);
setCallModel(Math.sqrt);
setCallModel(Math.abs);

exports.getBuiltinShim = function(concreteFn, isConstructor) {
    switch (concreteFn) {
        case String:
            if (isConstructor) {
                return function(...args) {
                    if (args.length === 0) {
                        return new String();
                    }
                    const cresult = new String(getConcrete(args[0]));
                    return new Concolic(cresult, new NewString(cresult, getSymbolic(args[0])));
                };
            } else {
                return function(...args) {
                    return args.length > 0 ? new Concolic(String(getConcrete(args[0])), new ToString(getSymbolic(args[0]))) : "";
                };
            }
        case Number:
            if (isConstructor) {
                return function(...args) {
                    if (args.length === 0) {
                        return new Number();
                    }
                    const result = new Number(getConcrete(args[0]));
                    return new Concolic(result, new NewNumber(result, getSymbolic(args[0])));
                };
            } else {
                return function(...args) {
                    return args.length > 0 ? new Concolic(Number(getConcrete(args[0])), new ToNumber(getSymbolic(args[0]))) : +0;
                };
            }
        case Array:
            return function(...args) {
                if (args.length === 1) {
                    const arg0 = args[0];
                    const carg0 = getConcrete(arg0),
                        sarg0 = getSymbolic(arg0);
                    // TODO: incorporate this type check as a constraint.
                    if (typeof carg0 === "number") {
                        const result = new Array(carg0);
                        return new Concolic(result, new NewArray(result, sarg0));
                    }
                    return [arg0];
                }

                return [...args];
            };
        case Boolean:
            if (isConstructor) {
                return function(value) {
                    const result = new Boolean(getConcrete(value));
                    return new Concolic(result, new NewBoolean(result, getSymbolic(value)));
                };
            } else {
                return function(value) {
                    return new Concolic(Boolean(getConcrete(value)), new ToBoolean(getSymbolic(value)));
                };
            }
        case Object:
            if (isConstructor) {
                return function(...args) {
                    if (args.length === 0) {
                        return {};
                    }
                    const cvalue = getConcrete(args[0]),
                        svalue = getSymbolic(args[0]);
                    const result = new Object(cvalue);
                    return new Concolic(result, new NewObject(result, svalue));
                };
            } else {
                return function(...args) {
                    if (args.length === 0) {
                        return {};
                    }
                    const cvalue = getConcrete(args[0]),
                        svalue = getSymbolic(args[0]);
                    const result = Object(cvalue);
                    return new Concolic(result, new ToObject(result, svalue));
                };
            }
        case RegExp:
            if (isConstructor) {
                return function(pattern, flags) {
                    const cpattern = getConcrete(pattern),
                        spattern = getSymbolic(pattern);
                    const cflags = getConcrete(flags),
                        sflags = getSymbolic(flags);
                    const result = new RegExp(cpattern, cflags);
                    return new Concolic(result, new NewRegExp(result, spattern, sflags));
                };
            } else {
                return function(pattern, flags) {
                    const cpattern = getConcrete(pattern);
                    const cflags = getConcrete(flags);
                    if (_.isRegExp(cpattern) && cflags === undefined) {
                        return pattern;
                    } else {
                        const spattern = getSymbolic(pattern);
                        const sflags = getSymbolic(flags);
                        const result = new RegExp(cpattern, cflags);
                        return new Concolic(result, new NewRegExp(result, spattern, sflags));
                    }
                };
            }
        case Function:
        case Date:
        case Error:
        case EvalError:
        case RangeError:
        case ReferenceError:
        case SyntaxError:
        case TypeError:
        case URIError:
            return null;
        default:
            return callModels.get(concreteFn);
    }
};
