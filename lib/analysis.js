/* global J$ */

(function(sandbox) {
    "use strict";

    // FIXME: Turn into external parameters.
    const CP_OPTS = {
        'mznPath': 'model.mzn',
        'dznPath': 'data.dzn',
        'fznPath': 'model.fzn',
        'mznTimeout': '3',
        'mzn2fznTimeout': '3',
        'fznTimeout': '3',
        'dumpTimeout': false, //timeout.mzn',
        'mznArgs': ['--no-output-ozn'],
        'mzn2fznArgs': ['--no-output-ozn', '-o', 'model.fzn'],
        'fznArgs': [],//['-max-alpha', '65535'], //['-max-length', '1000'],  //'-reverse-regex', 'false',
        'twoSteps': false,
        'solve': 'nobj_len', //'length', 'num_len', 'typs', 'typ_len', 'str_def', 'reps'
        'debug': false, //true,
        'abort': false,
        'verifyModel': false
    }
    
    const path = require("path");
    const process = require("process");
    const fs = require("fs");

    const _ = require("lodash");

    const {
        Concolic,
        isConcolic,
        concolizeObject,
        getConcrete,
        getSymbolic,
        setSymbolic,
        concretize
    } = require("./concolic");
    const { ExecutionPath, DSE } = require("./dse");
    const { doBinaryOp, doUnaryOp } = require("./ops");
    const {
        Constant,
        Variable,
        Binary,
        Unary,
        GetField,
        PutField,
        DeleteField,
        ToString,
        resetNameCounter
    } = require("./symbolic");
    const { getBuiltinShim } = require("./functionmodels");
    const Type = require("./type");
    const Z3 = require("./z3");
    const CVC4 = require("./cvc4");
    const G_Strings = require("./g-strings")
    const { get_cp_pid } = require("./cp")

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
        const concVal = inputs.hasOwnProperty(name) ? inputs[name] : getDefault(type);
        // FIXME: Check this.
        if (process.env.SOLVER !== "G-Strings" && !new Type(type).valueConforms(concVal)) {
            throw new Error("type error: " + name + " is not of type " + type);
        }
        inputs[name] = concVal;
        const symVal = new Variable(name, type);
        if (_.isObject(concVal)) {
            setSymbolic(concVal, symVal);
            return concVal;
        } else {
            return new Concolic(concVal, symVal);
        }
    }

    class ProcessExitException extends Error {}

    function createSolver(commandLog = null) {
        const SOLVER = process.env.SOLVER || "G-Strings";

        let solver;
        switch (SOLVER) {
            case "z3":
                solver = new Z3(process.env.Z3_PATH || "z3");
                break;
            case "cvc4":
                solver = new CVC4(process.env.CVC4_PATH || "cvc4", "QF_AUFBVDTSNIA");
                break;
            case "G-Strings":
                solver = new G_Strings(CP_OPTS);
                break;
            default:
                throw new Error(`invalid solver ${SOLVER}`);
        }        
        
        if (solver.isCPSolver()) {
            if (process.env.INCREMENTAL === "0")
                console.error("Warning: incremental option disabled for CP solvers.");
        }
        else {
            if (commandLog) {
                solver.logCommands(commandLog);
            }
            const theoryFiles = [SOLVER + "/prelude.smt2", "common.smt2"];
            for (let i = 0; i < theoryFiles.length; i++) {
                theoryFiles[i] = path.resolve(__dirname, "smt2", theoryFiles[i]);
            }
            solver.loadFiles(theoryFiles);
        }

        return solver;
    }

    function isFunctionInstrumented(f) {
        return f.hasOwnProperty(sandbox.Constants.SPECIAL_PROP_IID) ||
            f === sandbox.readInput || f === sandbox.readString ||
            f === sandbox.readNumber || f === sandbox.readBoolean ||
            f === sandbox.readObject || f === sandbox.check ||
            f === sandbox.assert;
    }

    class Jalangi2DSEAnalysis {
        async runAnalysis(maxIterations, cb) {
            let receivedSigint = false,
                timedOut = false;
            process.on("SIGINT", () => {
                receivedSigint = true;
                console.log("analysis: received SIGINT, terminating");
                console.log(process.kill(-get_cp_pid(), 'SIGINT'));
            });

            const analysisTimeout = parseInt(process.env.ANALYSIS_TIMEOUT, 10) || 0;
            if (analysisTimeout > 0) {
                const analysisTimer = setTimeout(function() { timedOut = true; }, analysisTimeout * 1000);
                analysisTimer.unref(); // Don't let this stall the event loop.
            }

            const dseOptions = {
                unsatCores: process.env.UNSAT_CORES === "1",
                incremental: !(process.env.SOLVER === "G-Strings") && 
                             !(process.env.INCREMENTAL === "0"),
            };

            sandbox.readInput = () => {
                return getVariable(this.inputs, Type.TOP);
            };

            sandbox.readString = () => {
                return getVariable(this.inputs, Type.STRING);
            };

            sandbox.readNumber = () => {
                return getVariable(this.inputs, Type.NUMBER);
            };

            sandbox.readBoolean = () => {
                return getVariable(this.inputs, Type.BOOLEAN);
            };

            sandbox.readObject = () => {
                return getVariable(this.inputs, Type.OBJECT);
            };

            sandbox.check = (cond) => {
                const value = this.conditional(null, cond);
                return value ? value.result : cond;
            };
            
            sandbox.assert = (cond) => {
                if(!sandbox.check(cond)) {
                    throw new ProcessExitException("J$.assert(): failed");
                }
                return cond;
            };

            sandbox.choose = (arr) => {
                arr = getConcrete(arr);
                if (arr.length > 1) {
                    let i;
                    for(i = 0; i < arr.length - 1; i++) {
                        const value = sandbox.check(sandbox.readBoolean());
                        if (getConcrete(value)) {
                            break;
                        }
                    }
                    return arr[i];
                } else {
                    return arr[0];
                }
            };

            const commandLog = process.env.SOLVER === "G-Strings" ?
                null
                :
                fs.createWriteStream("solver_commands.smt2");
            try {
                const solver = createSolver(commandLog);
                const inputLog = fs.openSync("inputlog.json", "w");
                let first = true;
                try {
                    fs.writeSync(inputLog, "[\n");
                    const searcher = new DSE(solver, (newInput) => {                    
                        if (!first) {
                            fs.writeSync(inputLog, ",\n");
                        }
                        first = false;
                        fs.writeSync(inputLog, JSON.stringify(newInput));
                        fs.fsyncSync(inputLog);
                    
                        this.inputs = newInput;
                        this.path = new ExecutionPath();
                        resetNameCounter();
                        try {
                            cb();
                        } catch (e) {
                            console.log("run terminated with exception:", e);
                        }

                        // Delete the cached copy of the script so it can be reloaded.
                        const inputFilename = process.argv[1];
                        delete require.cache[require.resolve(inputFilename)];
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
                  if (commandLog)
                      commandLog.end();
            }
        }

        conditional(iid, result) {
            if (isConcolic(result)) {
                const concVal = getConcrete(result);
                const symVal = getSymbolic(result);
                this.path.addConstraint(symVal, !!concVal);
                // If a === comparison between a concolic value and a concrete
                // value succeeds (or a !== fails), treat the concolic value as
                // if it was concrete from now on. This reduces the number of
                // constraints and thus avoids unnecessary solver calls, as well
                // as potentially saving some memory.
                if (symVal instanceof Binary &&
                    ((concVal && symVal.op === "===") || (!concVal && symVal.op === "!==")) &&
                    (symVal.left instanceof Constant || symVal.right instanceof Constant)) {
                    if (symVal.left instanceof Constant) {
                        symVal.right.forcedConstant = symVal.left;
                    } else {
                        symVal.left.forcedConstant = symVal.right;
                    }
                }
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
                return { result: getConcrete(val) };
            }
        }

        _with(iid, val) {
            // NOTE: This is the best we can do with the `with` statement. There
            // is no callback to indicate when we exit the `with` body, so even
            // if we tracked what names were introduced, we don't know when we
            // can release them in the same scope.
            if (isConcolic(val)) {
                return { result: getConcrete(val) };
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

        invokeFunPre(iid, f, base, args, isConstructor) {
            if (isConcolic(f)) {
                const symF = getSymbolic(f);
                if (symF instanceof GetField && !(symF.offset instanceof Constant)) {
                    const keyVal = String(symF.offset.eval(this.inputs));
                    if (symF.base instanceof Constant) {
                        this.path.addConstraint(new Binary("in", symF.offset, symF.base), keyVal in symF.base.value);
                        const keys = Object.keys(symF.base.value);
                        keys.sort();
                        for (const k of keys) {
                            this.path.addConstraint(new Binary("===", new ToString(symF.offset), new Constant(k)), k === keyVal);
                            if (k === keyVal)
                                break;
                        }
                    }
                }
            }

            const concF = getConcrete(f);
            if (!_.isFunction(concF) || isFunctionInstrumented(concF) || (!isConcolic(base) && !_.some(args, isConcolic))) {
                return { f: concF, base: base, args: args };
            }

            switch (concF) {
                case console.log:
                    return;
                case process.exit:
                    return {
                        f: function(code = 0) {
                            throw new ProcessExitException(code);
                        },
                        base: base,
                        args: args
                    };
            }

            const shim = getBuiltinShim(concF, isConstructor);
//            console.log(concF, isConstructor, shim)
            if (shim) {
                return { f: shim, base: base, args: args };
            } else if (shim === null) {
                console.warn("concretizing arguments to unmodelled native function", concF);
                return {
                    f: concF,
                    base: concretize(base),
                    args: _.map(args, concretize)
                };
            }

            // console.warn("concretizing globals: call to uninstrumented/unknown function", f);
            // concretize(global);
            console.warn("concretizing arguments to uninstrumented/unknown native function", concF);
            return {
                f: concF,
                base: concretize(base),
                args: _.map(args, concretize)
            };
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
//                console.dir(["putFieldPre", base, offset, val], {depth:null});
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


    sandbox.analysis = new Jalangi2DSEAnalysis();
})(J$);
