/* global J$ */

(function(sandbox) {
    "use strict";

    const process = require("process");

    const {Concolic, getConcrete, getSymbolic} = require("./concolic");
    const dse = require("./dse");
    const {doBinaryOp, doUnaryOp} = require("./ops");
    const symbolic = require("./symbolic");
    const Variable = symbolic.Variable,
        Binary = symbolic.Binary,
        Unary = symbolic.Unary,
        GetField = symbolic.GetField,
        PutField = symbolic.PutField;
    const Type = require("./type");
    const Z3 = require("./z3");

    class Jalangi2DSEAnalysis {
        async runAnalysis(maxIterations, cb) {
            const SOLVER_PATH = "../../z3/z3-4.5.0-x64-win/bin/z3";
            const ES_THEORY_PATH = "ecmascript.smt2";

            this.path = new dse.ExecutionPath();

            const solver = new Z3(SOLVER_PATH, ES_THEORY_PATH);
            try {
                const searcher = new dse.DSE(solver, (newInput) => {
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
            if (result instanceof Concolic) {
                this.path.addConstraint(result.symVal, result.concVal);
                return { result: result.concVal };
            }
        }

        binaryPre(iid, op, left, right) {
            if (left instanceof Concolic || right instanceof Concolic) {
                return { op: op, left: left, right: right, skip: true };
            }
        }

        binary(iid, op, left, right) {
            if (left instanceof Concolic || right instanceof Concolic) {
                const concResult = doBinaryOp(op, getConcrete(left), getConcrete(right));
                return { result: new Concolic(concResult, new Binary(op, getSymbolic(left), getSymbolic(right))) };
            }
        }

        unaryPre(iid, op, left) {
            if (left instanceof Concolic) {
                return { op: op, left: left, skip: true };
            }
        }

        unary(iid, op, left) {
            if (left instanceof Concolic) {
                const concResult = doUnaryOp(op, left.concVal);
                return { result: new Concolic(concResult, new Unary(op, left.symVal)) };
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
            if (base instanceof Concolic) {
                const baseType = typeof base.concVal;
                const isValid = baseType !== "undefined" && baseType !== "null";
                this.path.addTypeConstraint(
                    new Type(~(Type.UNDEFINED | Type.NULL)), base.symVal, isValid);
            }

            if (offset instanceof Concolic || base instanceof Concolic) {
                return { base: base, offset: offset, skip: true };
            }
        }

        getField(iid, base, offset) {
            if (offset instanceof Concolic || base instanceof Concolic) {
                const cbase = getConcrete(base);
                const coffset = getConcrete(offset);
                const sbase = getSymbolic(base);
                const soffset = getSymbolic(offset);

                return { result: new Concolic(cbase[coffset], new GetField(sbase, soffset)) };
            }
        }

        putFieldPre(iid, base, offset, val) {
            if (base instanceof Concolic) {
                const baseType = typeof base.concVal;
                const isValid = baseType !== "undefined" && baseType !== "null";
                this.path.addTypeConstraint(
                    new Type(~(Type.UNDEFINED | Type.NULL)), base.symVal, isValid);

                // Attach a PutField to our object value chain, and set the base
                // to the concrete object for the assignment.
                base.symVal = new PutField(base.symVal, offset, val);
                base = base.concVal;
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
