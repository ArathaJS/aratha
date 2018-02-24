/* global J$ */

(function(sandbox) {
    "use strict";

    const path = require("path");
    const process = require("process");
    const fs = require("fs");

    const _ = require("lodash");

    const { Concolic, isConcolic, concolizeObject, getConcrete, getSymbolic, setSymbolic, concretize, shallowConcretize } = require("./concolic");
    const { ExecutionPath, ExecutionPathSet, DSE } = require("./dse");
    const { doBinaryOp, doUnaryOp } = require("./ops");
    const { Variable, Binary, Unary, GetField, PutField, DeleteField, StringToString, StringConcat, StringCharAt, StringSubstring, StringSlice, StringIndexOf, StringSearch, StringReplace, RegExpTest, ObjectConstruct, ObjectCast, ArrayConstruct, StringObjectConstruct, StringCast } = require("./symbolic");
    const Type = require("./type");
    const Z3 = require("./z3");
    const CVC4 = require("./cvc4");

    const overrides = new Map();
    function getOverride(f, base, params) {
        const override = overrides.get(f);
        if (override) {
            return override.bind(base, params);
        }
    }

    let varNameCounter = 0;

    function getDefault(type) {
        if (Type.UNDEFINED & type) {
            return undefined;
        }

        if (Type.NULL & type) {
            return null;
        }

        if (Type.NUMBER & type) {
            return 0;
        }

        if (Type.BOOLEAN & type) {
            return false;
        }

        if (Type.STRING & type) {
            return "";
        }

        if (Type.OBJECT & type) {
            return {};
        }

        throw new Error("can't generate default for bottom type");
    }

    function getVariable(inputs, type) {
        const name = "var" + varNameCounter++;
        let concVal = inputs.hasOwnProperty(name) ? inputs[name] : getDefault(type);
        const symVal = new Variable(name, type);
        if (_.isObject(concVal)) {
            setSymbolic(concVal, new Variable(name));
            return concVal;
        } else {
            return new Concolic(concVal, symVal);
        }
    }

    sandbox.readInput = function() {
        throw new Error("invalid call of readInput");
    };

    overrides.set(sandbox.readInput, function(params) {
        return getVariable(params.inputs, Type.TOP);
    });

    sandbox.readString = function() {
        throw new Error("invalid call of readString");
    };

    overrides.set(sandbox.readString, function(params) {
        return getVariable(params.inputs, Type.STRING);
    });

    sandbox.readNumber = function() {
        throw new Error("invalid call of readNumber");
    };

    overrides.set(sandbox.readNumber, function(params) {
        return getVariable(params.inputs, Type.NUMBER);
    });

    sandbox.readBoolean = function() {
        throw new Error("invalid call of readBoolean");
    };

    overrides.set(sandbox.readBoolean, function(params) {
        return getVariable(params.inputs, Type.BOOLEAN);
    });

    sandbox.readObject = function() {
        throw new Error("invalid call of readObject");
    };

    overrides.set(sandbox.readObject, function(params) {
        return getVariable(params.inputs, Type.OBJECT);
    });

    overrides.set(console.log, function(params, ...args) {
        console.log(...args);
    });

    class ProcessExitException extends Error {}

    overrides.set(global.process.exit, function(params, code=0) {
        throw new ProcessExitException(code);
    });

    function overrideFunction(f, symbolicOp) {
        overrides.set(f, function(params, ...args) {
            const cbase = getConcrete(this), sbase = getSymbolic(this);
            const cargs = _.map(args, getConcrete), sargs = _.map(args, getSymbolic);
            return new Concolic(f.apply(cbase, cargs), new symbolicOp(sbase, ...sargs));
        });
    }

    overrideFunction(String.prototype.toString, StringToString);
    overrideFunction(String.prototype.valueOf, StringToString);
    overrideFunction(String.prototype.charAt, StringCharAt);
    overrideFunction(String.prototype.substring, StringSubstring);
    overrideFunction(String.prototype.slice, StringSlice);
    overrideFunction(String.prototype.indexOf, StringIndexOf);
    overrideFunction(String.prototype.search, StringSearch);
    overrideFunction(String.prototype.replace, StringReplace);
    overrideFunction(RegExp.prototype.test, RegExpTest);

    overrides.set(String.prototype.search, function(params, searchValue) {
        const csearchValue = getConcrete(searchValue);
        const cresult = String.prototype.search.call(getConcrete(this), csearchValue);
        if (_.isRegExp(csearchValue)) {
            return cresult;
        } else {
            return new Concolic(cresult, new StringSearch(getSymbolic(this), getSymbolic(searchValue)));
        }
    });

    overrides.set(String.prototype.replace, function(params, searchValue, replaceValue) {
        const csearchValue = getConcrete(searchValue);
        const creplaceValue = getConcrete(replaceValue);
        const cresult = String.prototype.replace.call(getConcrete(this), csearchValue, creplaceValue);
        if (_.isRegExp(csearchValue) || _.isFunction(creplaceValue)) {
            return cresult;
        } else {
            return new Concolic(cresult, new StringReplace(getSymbolic(this), getSymbolic(searchValue), getSymbolic(replaceValue)));
        }
    });

    overrides.set(String.prototype.concat, function(params, ...args) {
        const cbase = getConcrete(this), sbase = getSymbolic(this);
        const cargs = _.map(args, getConcrete), sargs = _.map(args, getSymbolic);
        // TODO: add type constraint on the base as per spec.
        return new Concolic(String.prototype.concat.apply(cbase, cargs), new StringConcat(sbase, sargs));
    });

    overrides.set(Object, function(params, value) {
        const cvalue = getConcrete(value), svalue = getSymbolic(value);
        if (params.isConstructor) {
            const result = new Object(cvalue);
            return new Concolic(result, new ObjectConstruct(result, getSymbolic(value)));
        } else {
            const result = Object(cvalue);
            return new Concolic(result, new ObjectCast(result, svalue));
        }
    });

    overrides.set(Array, function(params, ...args) {
        if (args.length >= 2) {
            return new Array(...args);
        } else if (args.length === 1) {
            const len = args[0];
            const result = new Array(getConcrete(len));
            return new Concolic(result, new ArrayConstruct(result, getSymbolic(len)));
        }
    });

    overrides.set(String, function(params, ...args) {
        if (args.length === 0)
            return "";
        const value = args[0];
        const cvalue = getConcrete(value), svalue = getSymbolic(value);
        if (params.isConstructor) {
            const result = new String(cvalue);
            return new Concolic(result, new StringObjectConstruct(result, getSymbolic(value)));
        } else {
            return new Concolic(String(cvalue), new StringCast(svalue));
        }
    });

    overrides.set(String.prototype.split, function(params, separator, limit) {
        return String.prototype.split.call(getConcrete(this), getConcrete(separator), getConcrete(limit));
    });

    function createConcBasePassArgs(f) {
        return function concBasePassArgs(params, ...args) {
            if(!isConcolic(this)) {
                return f.apply(this, args);
            } else {
                return f.apply(shallowConcretize(this), args);
            }
        };
    }

    function overrideConcBasePassArgs(f) {
        overrides.set(f, createConcBasePassArgs(f));
    }

    overrideConcBasePassArgs(Array.prototype.shift);
    overrideConcBasePassArgs(Array.prototype.unshift);
    overrideConcBasePassArgs(Array.prototype.push);
    overrideConcBasePassArgs(Array.prototype.filter);
    overrideConcBasePassArgs(Array.prototype.join);

    overrides.set(RegExp, function(params, ...args) {
        if (params.isConstructor) {
            return new RegExp(..._.map(args, getConcrete));
        } else {
            return RegExp(..._.map(args, getConcrete));
        }
    });

    overrides.set(Math.sin, function(params, arg) {
        return Math.sin(getConcrete(arg));
    });
    overrides.set(Math.cos, function(params, arg) {
        return Math.cos(getConcrete(arg));
    });
    overrides.set(Math.sqrt, function(params, arg) {
        return Math.sqrt(getConcrete(arg));
    });
    overrides.set(Math.abs, function(params, arg) {
        return Math.abs(getConcrete(arg));
    });

    overrides.set(String.prototype.charCodeAt, function(params, arg) {
        return String.prototype.charCodeAt.call(getConcrete(this), getConcrete(arg));
    });

    overrides.set(Number.prototype.toString, function(params, ...args) {
        const cbase = getConcrete(this), sbase = getSymbolic(this);
        return new Concolic(Number.prototype.toString.apply(cbase, args), new StringCast(sbase));
    });

    overrides.set(String.prototype.trim, function(params) {
        const cbase = getConcrete(this), sbase = getSymbolic(this);
        const cresult = String.prototype.trim.call(cbase);
        if (cbase === cresult) {
            return this;
        } else {
            return cresult;
        }
    });

    overrides.set(String.prototype.match, function(params, regexp) {
        const cbase = getConcrete(this), sbase = getSymbolic(this);
        return String.prototype.match.call(cbase, getConcrete(regexp));
    });

    function createSolver(commandLog=null) {
        const SMT_SOLVER = process.env.SMT_SOLVER || "cvc4";

        let solver;
        switch (SMT_SOLVER) {
            case "z3":
                solver = new Z3(process.env.Z3_PATH || "z3");
                break;
            case "cvc4":
                solver = new CVC4(process.env.CVC4_PATH || "cvc4", "QF_AUFBVDTSNIA");
                break;
            default:
                throw new Error(`invalid solver ${SMT_SOLVER}`);
        }

        if (commandLog) {
            solver.logCommands(commandLog);
        }

        const theoryFiles = [SMT_SOLVER + "/prelude.smt2", "common.smt2", SMT_SOLVER + "/bitwise.smt2"];
        for (let i = 0; i < theoryFiles.length; i++) {
            theoryFiles[i] = path.resolve(__dirname, "smt2", theoryFiles[i]);
        }
        solver.loadFiles(theoryFiles);

        return solver;
    }

    class Jalangi2DSEAnalysis {
        async runAnalysis(maxIterations, cb) {
            let receivedSigint = false, timedOut = false;
            process.on("SIGINT", () => {
                receivedSigint = true;
                console.log("analysis: received SIGINT, terminating");
            });

            const analysisTimeout = parseInt(process.env.ANALYSIS_TIMEOUT, 10) || 0;
            if (analysisTimeout > 0) {
                const analysisTimer = setTimeout(function() { timedOut = true; }, analysisTimeout * 1000);
                analysisTimer.unref(); // Don't let this stall the event loop.
            }

            const dseOptions = {
                unsatCores: process.env.UNSAT_CORES === "1",
                incremental: !(process.env.INCREMENTAL === "0"),
            };

            const commandLog = fs.createWriteStream("solver_commands.smt2");
            try {
                const solver = createSolver(commandLog);
                const inputLog = fs.openSync("inputlog.json", "w");
                let first = true;
                let visited = new ExecutionPathSet();
                try {
                    fs.writeSync(inputLog, "[\n");
                    const searcher = new DSE(solver, (newInput) => {
                        this.inputs = newInput;
                        this.path = new ExecutionPath();

                        try {
                            cb();
                        } catch (e) {
                            console.log("run terminated with exception:", e);
                        }

                        // Delete the cached copy of the script so it can be reloaded.
                        const inputFilename = process.argv[1];
                        delete require.cache[require.resolve(inputFilename)];

                        // if (!visited.hasPrefix(this.path.constraints)) {
                            // visited.add(this.path.constraints);
                            if (!first) {
                                fs.writeSync(inputLog, ",\n");
                            }
                            first = false;
                            fs.writeSync(inputLog, JSON.stringify(newInput));
                            fs.fsyncSync(inputLog);
                        // }

                        return this.path;
                    }, dseOptions);

                    let i = 0;
                    for (i = 0; i < maxIterations && !receivedSigint && !timedOut && !searcher.isDone(); i++) {
                        varNameCounter = 0;
                        await searcher.execute();
                    }

                    if (searcher.isDone()) {
                        console.log("finished: no more constraints to solve");
                    } else if (i >= maxIterations) {
                        console.log("finished: reached iteration limit");
                    } else if (receivedSigint) {
                        console.log("terminated: received SIGINT");
                    } else if (timedOut) {
                        console.log("terminated: timed out");
                    }
                } finally {
                    solver.close();
                    fs.writeSync(inputLog, "\n]\n");
                    fs.closeSync(inputLog);
                }
            } finally {
                commandLog.end();
            }
        }

        conditional(iid, result) {
            if (isConcolic(result)) {
                const concVal = getConcrete(result);
                this.path.addConstraint(getSymbolic(result), concVal);
                return { result: concVal };
            }
        }

        forinObject(iid, val) {
            // NOTE: The ES5 spec leaves the iteration order of for-in
            // statements up to the implementation. Since Jalangi does not allow
            // us to influence the iteration, we must concretize the iterand.
            //
            // A for-in loop will visit every property that existed at the start
            // of the loop exactly once, though properties deleted before they
            // are visited will not be visited at all. Properties added during
            // the iteration may or may not be iterated over.
            //
            // However, the annotation on https://es5.github.io/#x12.6.4 states
            // that all modern browsers iterate in insertion order, so we may be
            // able to do something useful after all.
            if (isConcolic(val)) {
                return {result: getConcrete(val)};
            }
        }

        _with(iid, val) {
            // NOTE: This is the best we can do with the `with` statement. There
            // is no callback to indicate when we exit the `with` body, so even
            // if we tracked what names were introduced, we don't know when we
            // can release them in the same scope.
            if (isConcolic(val)) {
                return {result: getConcrete(val)};
            }
        }

        binaryPre(iid, op, left, right) {
            if (isConcolic(left) || isConcolic(right)) {
                return { op: op, left: left, right: right, skip: true };
            }
        }

        binary(iid, op, left, right) {
            if (isConcolic(left) || isConcolic(right)) {
                if (op === "instanceof") { // We can't handle prototypes, so we have to concretize instanceof.
                    return { result: getConcrete(left) instanceof getConcrete(right) };
                }

                const concResult = doBinaryOp(op, getConcrete(left), getConcrete(right));
                if (op === "delete") {
                    setSymbolic(left, new DeleteField(getSymbolic(left), getSymbolic(right)));
                }
                return { result: new Concolic(concResult, new Binary(op, getSymbolic(left), getSymbolic(right))) };
            }
        }

        unaryPre(iid, op, left) {
            if (isConcolic(left)) {
                return { op: op, left: left, skip: true };
            }
        }

        unary(iid, op, left) {
            if (isConcolic(left)) {
                const concResult = doUnaryOp(op, getConcrete(left));
                return { result: new Concolic(concResult, new Unary(op, getSymbolic(left))) };
            }
        }

        invokeFunPre(iid, f, base, args, isConstructor, isMethod, functionIid) {
            f = getConcrete(f);
            if (f !== J$.readInput && f !== J$.readString && f !== J$.readNumber
                && f !== J$.readBoolean && f !== J$.readObject
                && !isConcolic(base) && !_.some(args, isConcolic)) {
                return {f: f, base: base, args: args};
            }
            if (functionIid === undefined) {
                const override = getOverride(f, base, {inputs: this.inputs,
                    iid: iid, isConstructor: isConstructor});
                if (override) {
                    return {f: override, base: base, args: args};
                } else {
                    console.log("uninstrumented function", f);
                    concretize(global);
                    return {f: f, base: concretize(base), args: _.map(args, concretize)};
                }
            }
            return {f: f, base: base, args: args};
        }

        getFieldPre(iid, base, offset) {
            if (isConcolic(base)) {
                const baseType = typeof getConcrete(base);
                const isValid = baseType !== "undefined" && baseType !== "null";
                this.path.addTypeConstraint(
                    new Type(~(Type.UNDEFINED | Type.NULL)), getSymbolic(base), isValid);
            }

            if (isConcolic(base) || isConcolic(offset)) {
                return { base: base, offset: offset, skip: true };
            }
        }

        getField(iid, base, offset) {
            if (isConcolic(base) || isConcolic(offset)) {
                const cbase = getConcrete(base);
                const coffset = getConcrete(offset);
                const sbase = getSymbolic(base);
                const soffset = getSymbolic(offset);

                const simplified = GetField.simplify(sbase, soffset);
                if (simplified) {
                    return simplified;
                }

                return { result: new Concolic(cbase[coffset], new GetField(sbase, soffset)) };
            }
        }

        putFieldPre(iid, base, offset, val) {
            if (isConcolic(offset) && !isConcolic(base)) {
                concolizeObject(base);
            }

            if (isConcolic(base)) {
                const baseConcVal = getConcrete(base);
                const baseType = typeof baseConcVal;
                const isValid = baseType !== "undefined" && baseType !== "null";
                const baseSymVal = getSymbolic(base);
                this.path.addTypeConstraint(
                    new Type(~(Type.UNDEFINED | Type.NULL)), baseSymVal, isValid);

                // Attach a PutField to our object value chain, and set the base
                // to the concrete object for the assignment.
                setSymbolic(base, new PutField(baseSymVal, getSymbolic(offset), getSymbolic(val)));
                base = baseConcVal;
            }

            return { base: base, offset: getConcrete(offset), val: val };
        }

        onReady(cb) {
            const MAX_ITERATIONS = 1024;
            this.runAnalysis(MAX_ITERATIONS, cb).catch((e) => {
                console.error("analysis terminated with exception:", e);
            });
        }
    }


    J$.analysis = new Jalangi2DSEAnalysis();
})(J$);
