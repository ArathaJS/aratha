/* global J$ */

(function(sandbox) {
    "use strict";

    const child_process = require("child_process");
    const _ = require("lodash");
    const EventEmitter = require("events");
    const fs = require("fs");

    class ExecutionPath {
        constructor(constraints) {
            this.constraints = constraints || [];
        }

        isEmpty() { return this.constraints.length === 0; }

        addConstraint(expr, concreteValue) {
            if (!_.some(this.constraints,
                    (other) => _.isEqual(expr, other.expr))) {
                this.constraints.push({
                    expr: expr,
                    value: concreteValue
                });
            }
        }

        clear() { this.constraints.length = 0; }
    }

    class ExecutionPathSet {
        constructor() {
            this._paths = new Set();
        }

        add(path) { this._paths.add(this._encode(path)); return this; }

        has(path) { return this._paths.has(this._encode(path)); }

        _encode(path) {
            return _.map(path.constraints,
                (c) => (c.value ? "" : "!") + c.expr.iid).join("$");
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
        declarationFormula() { return ["declare-const", this.name, "Val"]; }
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

    const MAX_INPUTS = 2;
    const SOLVER_PATH = "../../z3/z3-4.5.0-x64-win/bin/z3";
    const ES_THEORY_PATH = "ecmascript.smt2";

    const sexpr = require("./sexpr");

    class Z3Solver extends EventEmitter {
        constructor() {
            super();

            const z3 = child_process.spawn(SOLVER_PATH, ["-smt2", "-in"]);
            z3.stdin.write(fs.readFileSync(ES_THEORY_PATH));

            z3.stdout.setEncoding("utf8");

            const parser = new sexpr.Parser();
            z3.stdout.on("data", (data) => {
                parser.parse(data, (expr) => {
                    this.emit("output", expr);
                });
            });

            this.process = z3;
        }

        push(n) {
            this.submitCommands([
                ["push", n.toString()]
            ]);
        }

        pop(n) {
            this.submitCommands([
                ["pop", n.toString()]
            ]);
        }

        submitCommands(commands) {
            const commandString = _.map(commands, sexpr.stringify).join("\n") + "\n";
            console.log(commandString.trim());
            this.process.stdin.write(commandString);
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


    function generateSolverCommands(path, variables) {
        const commands = [];

        _.forEach(variables, (v) => {
            commands.push(v.declarationFormula());
            if (!v.type.trivial()) {
                commands.push(["assert", v.type.constraintFor(v)]);
            }
        });

        _.forEach(path.constraints, (c) => {
            const formula = c.expr.toFormula();
            if (c.value) {
                commands.push(["assert", formula]);
            } else {
                commands.push(["assert", ["not", formula]]);
            }
        });

        commands.push(["check-sat"]);
        return commands;
    }

    function parseVarName(varName) {
        // Slice off the 'var' prefix.
        return varName.slice(3);
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
                return parseFloat(contents, 10);
            case "Str":
                return contents;
            default:
                throw new Error("invalid value type " + value.toString());
        }
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
            solver.on("output", (expr) => {
                console.log(expr);
            });

            this.path = new ExecutionPath();

            function solvePath(path, callback) {
                const variables = collectVariables(_.map(path.constraints, "expr"));

                solver.once("output", (status) => {
                    if (status === "sat") {
                        solver.submitCommands([
                            ["get-value", _.map(variables, (v) => v.toFormula())]
                        ]);
                        solver.pop(1);

                        solver.once("output", (assignment) => {
                            const solution = {};
                            for (let j = 0; j < assignment.length; j++) {
                                const name = assignment[j][0],
                                    value = assignment[j][1];
                                solution[parseVarName(name)] = parseVal(value);
                            }
                            callback(status, solution);
                        });
                    } else {
                        callback(status);
                        solver.pop(1);
                    }
                });

                solver.push(1);
                solver.submitCommands(generateSolverCommands(path, variables));
            }

            const inputQueue = [{}];
            const pathSet = new ExecutionPathSet();

            function generateInputs(oldPath, callback, i) {
                if (i >= oldPath.constraints.length) {
                    callback();
                    return;
                }

                const newPath = new ExecutionPath(oldPath.constraints.slice(0, i + 1));
                newPath.constraints[i].value = !newPath.constraints[i].value;

                if (!pathSet.has(newPath)) {
                    pathSet.add(newPath);
                    solvePath(newPath, (status, solution) => {
                        if (solution !== undefined) {
                            inputQueue.push(solution);
                        }
                        // Reset the value since it's the same object as in
                        // oldPath.
                        newPath.constraints[i].value = !newPath.constraints[i].value;

                        generateInputs(oldPath, callback, i + 1);
                    });
                } else {
                    generateInputs(oldPath, callback, i + 1);
                }
            }

            const process = require("process");

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
                cb();
                pathSet.add(this.path);

                // Delete the cached copy of the script so it can be reloaded.
                const input_filename = process.argv[1];
                delete require.cache[require.resolve(input_filename)];

                generateInputs(this.path, () => runAnalysis(n - 1), 0);
            };

            runAnalysis(MAX_INPUTS);
        }
    };

    sandbox.readInput = function() {
        throw new Error("invalid call of readInput");
    };

})(J$);
