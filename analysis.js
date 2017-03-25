/* global J$ */

(function(sandbox) {
    "use strict";

    const process = require("process");

    const dse = require("./dse");
    const symbolic = require("./symbolic");
    const SymbolicValue = symbolic.SymbolicValue,
        Variable = symbolic.Variable,
        Binary = symbolic.Binary,
        Unary = symbolic.Unary,
        GetField = symbolic.GetField;
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
            if (result instanceof SymbolicValue) {
                const value = result.eval();
                this.path.addConstraint(result, value);
                return { result: value };
            }
        }

        binaryPre(iid, op, left, right) {
            if ((left instanceof SymbolicValue) || (right instanceof SymbolicValue)) {
                return { op: op, left: left, right: right, skip: true };
            }
        }

        binary(iid, op, left, right) {
            if ((left instanceof SymbolicValue) || (right instanceof SymbolicValue)) {
                return { result: new Binary(iid, op, left, right) };
            }
        }

        unaryPre(iid, op, left) {
            if ((left instanceof SymbolicValue)) {
                return { op: op, left: left, skip: true };
            }
        }

        unary(iid, op, left) {
            if ((left instanceof SymbolicValue)) {
                return { result: new Unary(iid, op, left) };
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
                return { result: new Variable("var" + giid, this.inputs[giid]) };
            }
        }

        getFieldPre(iid, base, offset) {
            if (base instanceof SymbolicValue || offset instanceof SymbolicValue) {
                return { base: base, offset: offset, skip: true };
            }
        }

        getField(iid, base, offset) {
            if (base instanceof SymbolicValue || offset instanceof SymbolicValue) {
                const cbase = base instanceof SymbolicValue ? base.eval() : base;
                const coffset = offset instanceof SymbolicValue ? offset.eval() : offset;

                if (base instanceof SymbolicValue) {
                    const baseType = typeof cbase;
                    const isValid = baseType !== "undefined" && baseType !== "null";
                    this.path.addTypeConstraint(
                        new Type(~(Type.UNDEFINED | Type.NULL)), base, isValid);
                }

                return { result: new GetField(iid, base, offset, cbase[coffset]) };
            }
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
