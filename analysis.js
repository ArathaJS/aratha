/* global J$ */

(function(sandbox) {
    "use strict";

    const child_process = require("child_process");
    const _ = require("lodash");
    const fs = require("fs");

    class Constraint {
        constructor(expr, value) {
            this.expr = expr;
            this.value = value;
        }

        negate() {
            this.value = !this.value;
        }

        toFormula() {
            const formula = this.expr.toFormula();
            return this.value ? formula : ["not", formula];
        }
    }

    class ExecutionPath {
        constructor(constraints) {
            this.constraints = constraints || [];
        }

        isEmpty() { return this.constraints.length === 0; }

        addConstraint(expr, concreteValue) {
            const constraint = new Constraint(expr, concreteValue);
            if (!_.some(this.constraints, constraint)) {
                this.constraints.push(constraint);
            }
        }

        clear() { this.constraints.length = 0; }

        getPrefix(length) {
            return new ExecutionPath(this.constraints.slice(0, length));
        }
    }

    class Trie {
        constructor() {
            this._root = {};
        }

        add(s) {
            let node = this._root;
            for (let i = 0; i < s.length; i++) {
                const w = s[i];
                if (!node.hasOwnProperty(w))
                    node[w] = {};
                node = node[w];
            }
        }

        hasPrefix(s) {
            let node = this._root;
            for (let i = 0; i < s.length; i++) {
                const w = s[i];
                if (!node.hasOwnProperty(w))
                    return false;
                node = node[w];
            }
            return true;
        }
    }

    class ExecutionPathSet {
        constructor() {
            this._paths = new Trie();
        }

        add(path) { this._paths.add(this._encode(path)); return this; }

        hasPrefix(path) { return this._paths.hasPrefix(this._encode(path)); }

        _encode(path) {
            return _.map(path.constraints,
                (c) => (c.value ? "" : "!") + c.expr.iid);
        }
    }

    const symbolic = require("./symbolic");
    const SymbolicValue = symbolic.SymbolicValue,
        Variable = symbolic.Variable,
        Binary = symbolic.Binary,
        Unary = symbolic.Unary;


    const smt = require("./smt");

    class Z3Solver extends smt.Solver {
        constructor(solver_path, theory_path) {
            const z3 = child_process.spawn(solver_path, ["-smt2", "-in"]);
            super(z3);
            z3.stdin.write(fs.readFileSync(theory_path));
        }
    }


    function collectVariables(expr) {
        const variables = {};

        if (expr instanceof SymbolicValue) {
            expr.visit((expr) => {
                if (expr instanceof Variable) {
                    variables[expr.name] = expr;
                }
            });
        } else {
            _.forEach(expr, (v) => Object.assign(variables, collectVariables(v)));
        }

        return variables;
    }

    function parseVarName(varName) {
        // Slice off the 'var' prefix.
        return varName.slice(3);
    }

    function parseNumericExpr(expr) {
        if (typeof expr === "string")
            return parseFloat(expr, 10);

        const args = _.map(expr.slice(1), parseNumericExpr);
        switch (expr[0]) {
            case "-":
                return _.reduce(args, (total, x) => total - x, 0);
            case "/":
                return args[0] / args[1];
            default:
                throw new Error("unknown operator " + expr[0]);
        }
    }

    function parseVal(value) {
        if (value === "undefined") { return undefined; }
        if (value === "null") { return null; }

        const type = value[0],
            contents = value[1];
        switch (type) {
            case "Boolean":
                return contents === "true";
            case "Num":
                return parseNumericExpr(contents);
            case "Str":
                return contents;
            default:
                throw new Error("invalid value type " + value.toString());
        }
    }

    function parseAssignment(assignment) {
        const solution = {};
        for (let j = 0; j < assignment.length; j++) {
            const name = assignment[j][0],
                value = assignment[j][1];
            solution[parseVarName(name)] = parseVal(value);
        }
        return solution;
    }

    function declareVar(solver, v) {
        solver.declareConst(v.name, "Val");
        if (!v.type.trivial()) {
            solver.assert(v.type.constraintFor(v.toFormula()));
        }
    }

    class DSE {
        constructor(solver, program) {
            this._solver = solver;
            this._program = program;
            this._inputs = [{}];
            this._visitedPaths = new ExecutionPathSet();
        }

        execute() {
            const input = this._nextInput();
            console.log("testing input: ", input);
            const path = this._program(input);
            console.log("executed path: ", this._visitedPaths._encode(path));
            return this._processPath(path);
        }

        isDone() {
            return this._inputs.length === 0;
        }

        _processPath(path) {
            this._visitedPaths.add(path);
            return this._generateInputsIncremental(path);
        }

        _nextInput() { return this._inputs.shift(); }

        _generateInputs(path) {
            const promises = [];
            const solver = this._solver;

            for (let i = 0; i < path.constraints.length; i++) {
                path.constraints[i].negate();
                const prefix = path.getPrefix(i + 1);
                if (!this._visitedPaths.hasPrefix(prefix)) {
                    solver.push(1);

                    const variables = collectVariables(prefix.constraints);
                    _.forEach(variables, (v) => declareVar(solver, v));
                    _.forEach(prefix.constraints, (c) => solver.assert(c.toFormula()));
                    solver.checkSat();
                    const p = solver.getValue(Object.keys(variables)).then((assignment) => {
                        this._inputs.push(parseAssignment(assignment));
                    }).catch(() => Promise.resolve());
                    promises.push(p);

                    solver.pop(1);
                }
                path.constraints[i].negate();
            }

            return Promise.all(promises);
        }

        _generateInputsIncremental(path) {
            const promises = [];
            const variables = {};
            const solver = this._solver;

            solver.push(1);
            for (let i = 0; i < path.constraints.length; i++) {
                const c = path.constraints[i];

                const freeVars = collectVariables(c);
                _.forEach(freeVars, (v, k) => {
                    if (!variables.hasOwnProperty(k)) {
                        variables[k] = v;
                        declareVar(solver, v);
                    }
                });

                c.negate();
                if (!this._visitedPaths.hasPrefix(path.getPrefix(i + 1))) {
                    solver.push(1);

                    solver.assert(c.toFormula());
                    solver.checkSat();
                    const p = solver.getValue(Object.keys(variables)).then((assignment) => {
                        this._inputs.push(parseAssignment(assignment));
                    }).catch(() => Promise.resolve());
                    promises.push(p);

                    solver.pop(1);
                }
                c.negate();

                if (i < path.constraints.length - 1) {
                    solver.assert(c.toFormula());
                }
            }
            solver.pop(1);

            return Promise.all(promises);
        }
    }

    class Jalangi2DSEAnalysis {
        async runAnalysis(maxIterations, cb) {
            const SOLVER_PATH = "../../z3/z3-4.5.0-x64-win/bin/z3";
            const ES_THEORY_PATH = "ecmascript.smt2";

            const process = require("process");

            this.path = new ExecutionPath();

            const solver = new Z3Solver(SOLVER_PATH, ES_THEORY_PATH);
            try {
                const dse = new DSE(solver, (newInput) => {
                    this.inputs = newInput;
                    this.path.clear();

                    cb();

                    // Delete the cached copy of the script so it can be reloaded.
                    const inputFilename = process.argv[1];
                    delete require.cache[require.resolve(inputFilename)];

                    return this.path;
                });

                let i = 0;
                for (i = 0; i < maxIterations && !dse.isDone(); i++) {
                    await dse.execute();
                }

                if (dse.isDone()) {
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

        onReady(cb) {
            const MAX_ITERATIONS = 5;
            this.runAnalysis(MAX_ITERATIONS, cb).catch((e) => console.error(e));
        }
    }


    J$.analysis = new Jalangi2DSEAnalysis();

    sandbox.readInput = function() {
        throw new Error("invalid call of readInput");
    };

})(J$);
