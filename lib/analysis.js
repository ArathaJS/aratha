/* global J$ */

(function(sandbox) {
    "use strict";

    const path = require("path");
    const process = require("process");

    const { Concolic, isConcolic, concolizeObject, getConcrete, getSymbolic, setSymbolic } = require("./concolic");
    const { ExecutionPath, DSE } = require("./dse");
    const { doBinaryOp, doUnaryOp } = require("./ops");
    const { Variable, Binary, Unary, GetField, PutField } = require("./symbolic");
    const Type = require("./type");
    const Z3 = require("./z3");
    const CVC4 = require("./cvc4");

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

        binaryPre(iid, op, left, right) {
            if (isConcolic(left) || isConcolic(right)) {
                return { op: op, left: left, right: right, skip: true };
            }
        }

        binary(iid, op, left, right) {
            if (isConcolic(left) || isConcolic(right)) {
                const concResult = doBinaryOp(op, getConcrete(left), getConcrete(right));
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

        invokeFunPre(iid, f, base, args) {
            if (f === sandbox.readInput) {
                return { f: f, base: base, args: args, skip: true };
            }
        }

        invokeFun(iid, f) {
            if (f === sandbox.readInput) {
                //var giid = J$.sid + "_" + iid;
                const giid = iid;
                const name = "var" + giid;
                return { result: new Concolic(this.inputs[name], new Variable(name)) };
            }
        }

        getFieldPre(iid, base, offset) {
            if (isConcolic(base)) {
                const baseType = getConcrete(base);
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

                return { result: new Concolic(cbase[coffset], new GetField(sbase, soffset)) };
            }
        }

        putFieldPre(iid, base, offset, val) {
            if (isConcolic(offset) && !isConcolic(base)) {
                concolizeObject(base, base);
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
            this.runAnalysis(MAX_ITERATIONS, cb).catch((e) => console.error(e));
        }
    }


    J$.analysis = new Jalangi2DSEAnalysis();

    sandbox.readInput = function() {
        throw new Error("invalid call of readInput");
    };

})(J$);
