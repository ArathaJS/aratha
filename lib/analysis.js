/* global J$ */

(function(sandbox) {
    "use strict";

    const path = require("path");
    const process = require("process");

    const _ = require("lodash");

    const { Concolic, isConcolic, concolizeObject, getConcrete, getSymbolic, setSymbolic, concretize } = require("./concolic");
    const { ExecutionPath, DSE } = require("./dse");
    const { doBinaryOp, doUnaryOp } = require("./ops");
    const { Variable, Binary, Unary, GetField, PutField, DeleteField, StringToString, StringConcat, StringCharAt, StringIndexOf, StringSearch } = require("./symbolic");
    const Type = require("./type");
    const Z3 = require("./z3");
    const CVC4 = require("./cvc4");

    sandbox.readInput = function() {
        throw new Error("invalid call of readInput");
    };

    const overrides = new Map();
    function getOverride(f, base, params) {
        const override = overrides.get(f);
        if (override) {
            return override.bind(base, params);
        }
    }

    overrides.set(sandbox.readInput, function(params) {
        const name = "var" + params.iid;
        const concVal = params.inputs[name];
        const symVal = new Variable(name);
        if (_.isObject(concVal)) {
            setSymbolic(concVal, new Variable(name));
            return concVal;
        } else {
            return new Concolic(concVal, symVal);
        }
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
    overrideFunction(String.prototype.indexOf, StringIndexOf);
    overrideFunction(String.prototype.search, StringSearch);

    overrides.set(String.prototype.concat, function(params, ...args) {
        const cbase = getConcrete(this), sbase = getSymbolic(this);
        const cargs = _.map(args, getConcrete), sargs = _.map(args, getSymbolic);
        // TODO: add type constraint on the base as per spec.
        return new Concolic(String.prototype.concat.apply(cbase, cargs), new StringConcat(sbase, sargs));
    });

    function createSolver() {
        const SMT_SOLVER = process.env.SMT_SOLVER || "cvc4";

        let solver;
        switch (SMT_SOLVER) {
            case "z3":
                solver = new Z3(process.env.Z3_PATH || "z3");
                break;
            case "cvc4":
                solver = new CVC4(process.env.CVC4_PATH || "cvc4", "QF_AUFBVDTSLIA");
                break;
            default:
                throw new Error(`invalid solver ${SMT_SOLVER}`);
        }

        const theoryFiles = ["common.smt2", SMT_SOLVER + "/bitwise.smt2"];
        for (let i = 0; i < theoryFiles.length; i++) {
            theoryFiles[i] = path.resolve(__dirname, "smt2", theoryFiles[i]);
        }
        solver.loadFiles(theoryFiles);

        return solver;
    }

    class Jalangi2DSEAnalysis {
        async runAnalysis(maxIterations, cb) {
            const solver = createSolver();
            this.path = new ExecutionPath();
            try {
                const searcher = new DSE(solver, (newInput) => {
                    this.inputs = newInput;
                    this.path.clear();

                    try {
                        cb();
                    } catch (e) {
                        console.log("run terminated with exception:", e);
                    }

                    // Delete the cached copy of the script so it can be reloaded.
                    const inputFilename = process.argv[1];
                    delete require.cache[require.resolve(inputFilename)];

                    return this.path;
                });

                let i = 0;
                for (i = 0; i < maxIterations && !searcher.isDone(); i++) {
                    await searcher.execute();
                }

                if (searcher.isDone()) {
                    console.log("finished: no more constraints to solve");
                } else if (i >= maxIterations) {
                    console.log("finished: reached iteration limit");
                }
            } finally {
                solver.close();
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
            if (functionIid === undefined) {
                const override = getOverride(f, base, {inputs: this.inputs,
                    iid: iid, isConstructor: isConstructor});
                if (override) {
                    return {f: override, base: base, args: args};
                } else {
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
            const MAX_ITERATIONS = 9;
            this.runAnalysis(MAX_ITERATIONS, cb).catch((e) => {
                setTimeout(() => { throw e; });
            });
        }
    }


    J$.analysis = new Jalangi2DSEAnalysis();
})(J$);
