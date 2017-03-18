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

    class SymbolicValue {
        constructor() {}

        eval() { return undefined; }
        visit(visitor) { visitor(this); }

        _visitChild(child, visitor) {
            if (child instanceof SymbolicValue) {
                child.visit(visitor);
            } else {
                visitor(child);
            }
        }
    }

    function escapeSMTString(s) {
        return '"' + s.replace('"', '""') + '"';
    }

    function valueToFormula(value) {
        if (value instanceof SymbolicValue) {
            return value.toFormula();
        }

        switch (typeof value) {
            case "undefined":
                return "undefined";
            case "null":
                return "null";
            case "boolean":
                return ["Boolean", value.toString()];
            case "number":
                if (value >= 0) {
                    return ["Num", value.toFixed(19)];
                } else {
                    return ["Num", ["-", (-value).toFixed(19)]];
                }
            case "string":
                return ["Str", escapeSMTString(value)];
            default:
                throw new Error("values of type " + typeof value + " not implemented");
        }
    }

    class Type {
        constructor(types) {
            if (types === undefined) {
                types = Type.TOP;
            }

            this.types = types;
        }

        requireTypes(types) { this.types &= types; }
        forbidTypes(types) { this.types &= ~types; }

        intersection(type) { return new Type(this.types & type.types); }

        valid() { return this.types !== Type.BOTTOM; }
        trivial() { return this.types === Type.TOP; }

        has(types) { return (this.types & types) !== Type.BOTTOM; }

        constraintFor(value) {
            const valFormula = valueToFormula(value);
            const negative = [];

            const predicates = Type.predicates;

            for (const k in predicates) {
                if (predicates.hasOwnProperty(k)) {
                    if (!this.has(k)) {
                        negative.push(predicates[k]);
                    }
                }
            }

            if (negative.length > 0) {
                const negativeFormula = _.map(negative, (x) => [x, valFormula]);
                negativeFormula.unshift("or");
                return ["not", negativeFormula];
            } else {
                return "true";
            }
        }
    }

    Type.UNDEFINED = 1;
    Type.NULL = 1 << 1;
    Type.BOOLEAN = 1 << 2;
    Type.STRING = 1 << 3;
    Type.NUMBER = 1 << 4;
    Type.OBJECT = 1 << 5;

    Type.TOP = ~(~0 << 6);
    Type.BOTTOM = 0;

    Type.predicates = {
        1: "is-undefined",
        2: "is-null",
        4: "is-Boolean",
        8: "is-Str",
        16: "is-Num",
        32: "is-Object"
    };

    class Variable extends SymbolicValue {
        constructor(name, concreteValue, type) {
            super();

            this.name = name;
            this.concreteValue = concreteValue;
            this.type = type || new Type();
        }

        eval() { return this.concreteValue; }
        toFormula() { return this.name; }
    }

    class Binary extends SymbolicValue {
        constructor(iid, op, left, right) {
            super();
            this.iid = iid; //J$.getGlobalIID(iid);
            this.op = op;
            this.left = left;
            this.right = right;
        }

        eval() {
            const op = this.op;
            let left = this.left,
                right = this.right,
                result;

            if (left instanceof SymbolicValue) {
                left = left.eval();
            }

            if (right instanceof SymbolicValue) {
                right = right.eval();
            }

            switch (op) {
                case "+":
                    result = left + right;
                    break;
                case "-":
                    result = left - right;
                    break;
                case "*":
                    result = left * right;
                    break;
                case "/":
                    result = left / right;
                    break;
                case "%":
                    result = left % right;
                    break;
                case "<<":
                    result = left << right;
                    break;
                case ">>":
                    result = left >> right;
                    break;
                case ">>>":
                    result = left >>> right;
                    break;
                case "<":
                    result = left < right;
                    break;
                case ">":
                    result = left > right;
                    break;
                case "<=":
                    result = left <= right;
                    break;
                case ">=":
                    result = left >= right;
                    break;
                case "==":
                    result = left == right;
                    break;
                case "!=":
                    result = left != right;
                    break;
                case "===":
                    result = left === right;
                    break;
                case "!==":
                    result = left !== right;
                    break;
                case "&":
                    result = left & right;
                    break;
                case "|":
                    result = left | right;
                    break;
                case "^":
                    result = left ^ right;
                    break;
                case "delete":
                    result = delete left[right];
                    break;
                case "instanceof":
                    result = left instanceof right;
                    break;
                case "in":
                    result = left in right;
                    break;
                default:
                    throw new Error(op + " at " + this.iid + " not found");
            }

            return result;
        }

        visit(visitor) {
            visitor(this);
            this._visitChild(this.left, visitor);
            this._visitChild(this.right, visitor);
        }

        toFormula() {
            return ["js." + this.op, valueToFormula(this.left), valueToFormula(this.right)];
        }
    }

    class Unary extends SymbolicValue {
        constructor(iid, op, expr) {
            super();
            this.iid = iid; //J$.getGlobalIID(iid);
            this.op = op;
            this.expr = expr;
        }

        eval() {
            const op = this.op;
            let expr = this.expr,
                result;

            if (expr instanceof SymbolicValue) {
                expr = expr.eval();
            }

            switch (op) {
                case "+":
                    result = +expr;
                    break;
                case "-":
                    result = -expr;
                    break;
                case "~":
                    result = ~expr;
                    break;
                case "!":
                    result = !expr;
                    break;
                case "typeof":
                    result = typeof expr;
                    break;
                case "void":
                    result = void(expr);
                    break;
                default:
                    throw new Error(op + " at " + this.iid + " not found");
            }

            return result;
        }

        visit(visitor) {
            visitor(this);
            this._visitChild(this.expr, visitor);
        }

        toFormula() { return ["js." + this.op, valueToFormula(this.expr)]; }
    }

    const MAX_INPUTS = 10;
    const SOLVER_PATH = "../../z3/z3-4.5.0-x64-win/bin/z3";
    const ES_THEORY_PATH = "ecmascript.smt2";

    const sexpr = require("./sexpr");

    class Z3Solver {
        constructor() {
            const z3 = child_process.spawn(SOLVER_PATH, ["-smt2", "-in"]);
            z3.stdin.write(fs.readFileSync(ES_THEORY_PATH));

            this._callbackQueue = [];

            z3.stdout.setEncoding("utf8");

            const parser = new sexpr.Parser();
            z3.stdout.on("data", (data) => {
                parser.parse(data, (stmt) => {
                    this._consume(stmt);
                });
            });

            this.process = z3;
        }

        push(n) {
            this._send(["push", n.toString()]);
        }

        pop(n) {
            this._send(["pop", n.toString()]);
        }

        checkSat() {
            this._send(["check-sat"]);
            return this._getResponse();
        }

        declareConst(name, sort) {
            this._send(["declare-const", name, sort]);
        }

        assert(formula) {
            this._send(["assert", formula]);
        }

        getValue(vars) {
            this._send(["get-value", vars]);
            return this._getResponse();
        }

        _send(command) {
            const cmdString = sexpr.stringify(command);
            console.log(cmdString);
            this.process.stdin.write(cmdString + "\n");
        }

        _enqueueCallback(callback) {
            this._callbackQueue.push(callback);
        }

        _consume(stmt) {
            (this._callbackQueue.shift())(stmt);
        }

        _getResponse() {
            return new Promise((resolve, reject) => {
                this._enqueueCallback((stmt) => {
                    if (stmt[0] !== "error") {
                        resolve(stmt);
                    } else {
                        reject(stmt[1]);
                    }
                });
            });
        }

        close() {
            this.process.stdin.end("(exit)");
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
        switch(expr[0]) {
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

    J$.analysis = {
        /**
         * This callback is called after a condition check before branching.
         * Branching can happen in various statements
         * including if-then-else, switch-case, while, for, ||, &&, ?:.
         *
         * @param {number} iid - Static unique instruction identifier of this callback
         * @param {*} result - The value of the conditional expression
         * @returns {{result: *}|undefined} - If an object is returned, the result of
         * the conditional expression is replaced with the value stored in the
         * <tt>result</tt> property of the object.
         */
        conditional: function(iid, result) {
            if (result instanceof SymbolicValue) {
                const value = result.eval();
                this.path.addConstraint(result, value);
                return { result: value };
            }
        },

        binaryPre: function(iid, op, left, right) {
            if ((left instanceof SymbolicValue) || (right instanceof SymbolicValue)) {
                return { op: op, left: left, right: right, skip: true };
            }
        },

        binary: function(iid, op, left, right) {
            if ((left instanceof SymbolicValue) || (right instanceof SymbolicValue)) {
                return { result: new Binary(iid, op, left, right) };
            }
        },

        unaryPre: function(iid, op, left) {
            if ((left instanceof SymbolicValue)) {
                return { op: op, left: left, skip: true };
            }
        },

        unary: function(iid, op, left) {
            if ((left instanceof SymbolicValue)) {
                return { result: new Unary(iid, op, left) };
            }
        },

        invokeFunPre: function(iid, f, base, args) {
            if (f === sandbox.readInput) {
                return { f: f, base: base, args: args, skip: true };
            }
        },

        invokeFun: function(iid, f) {
            if (f === sandbox.readInput) {
                //var giid = J$.sid + "_" + iid;
                const giid = iid;
                return { result: new Variable("var" + giid, this.inputs[giid]) };
            }
        },

        onReady: function(cb) {
            const solver = new Z3Solver();

            this.path = new ExecutionPath();

            const inputQueue = [{}];
            const visitedPaths = new ExecutionPathSet();

            function enqueueInput(input) {
                inputQueue.push(input);
            }

            function declareVar(v) {
                solver.declareConst(v.name, "Val");
                if (!v.type.trivial()) {
                    solver.assert(v.type.constraintFor(v));
                }
            }

            function generateInputs(path) {
                const promises = [];

                for (let i = 0; i < path.constraints.length; i++) {
                    path.constraints[i].negate();
                    const prefix = path.getPrefix(i + 1);
                    if (!visitedPaths.hasPrefix(prefix)) {
                        solver.push(1);

                        const variables = collectVariables(prefix.constraints);
                        _.forEach(variables, (v) => declareVar(v));
                        _.forEach(prefix.constraints, (c) => solver.assert(c.toFormula()));
                        solver.checkSat();
                        const p = solver.getValue(Object.keys(variables)).then((assignment) => {
                            enqueueInput(parseAssignment(assignment));
                        }).catch(() => Promise.resolve());
                        promises.push(p);

                        solver.pop(1);
                    }
                    path.constraints[i].negate();
                }

                return Promise.all(promises);
            }

            function generateInputsIncremental(path) {
                const promises = [];
                const variables = {};

                function declareNewVars(constraint) {
                    const freeVars = collectVariables(constraint);
                    _.forEach(freeVars, (v, k) => {
                        if (!variables.hasOwnProperty(k)) {
                            variables[k] = v;
                            declareVar(v);
                        }
                    });
                }

                solver.push(1);
                for (let i = 0; i < path.constraints.length; i++) {
                    const c = path.constraints[i];
                    declareNewVars(c);

                    c.negate();
                    if (!visitedPaths.hasPrefix(path.getPrefix(i + 1))) {
                        solver.push(1);

                        solver.assert(c.toFormula());
                        solver.checkSat();
                        const p = solver.getValue(Object.keys(variables)).then((assignment) => {
                            enqueueInput(parseAssignment(assignment));
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

            const process = require("process");

            const inputGenerator = generateInputsIncremental;
            // const inputGenerator = generateInputs;

            const runAnalysis = (n) => {
                if (inputQueue.length === 0) {
                    console.log("finished: no more constraints to solve");
                    solver.close();
                    return;
                }

                if (n <= 0) {
                    console.log("finished: reached iteration limit");
                    solver.close();
                    return;
                }

                this.path.clear();
                this.inputs = inputQueue.shift();
                console.log("testing input: ", this.inputs);
                cb();
                visitedPaths.add(this.path);
                console.log("executed path: ", visitedPaths._encode(this.path));

                // Delete the cached copy of the script so it can be reloaded.
                const input_filename = process.argv[1];
                delete require.cache[require.resolve(input_filename)];

                inputGenerator(this.path).then(() => runAnalysis(n - 1));
            };

            runAnalysis(MAX_INPUTS);
        }
    };

    sandbox.readInput = function() {
        throw new Error("invalid call of readInput");
    };

})(J$);
