/* global J$ */

(function(sandbox) {
    "use strict";

    const child_process = require("child_process");
    const _ = require("lodash");
    const EventEmitter = require("events");
    const fs = require("fs");

    const inputs = {};
    const constraints = [];

    function addConstraint(val) {
        if (!_.some(constraints, _.partial(_.isEqual, val))) {
            constraints.push(val);
        }
    }

    function stringifySExpression(expr) {
        if (typeof expr === "string") {
            return expr;
        }

        return "(" + _.join(_.map(expr, stringifySExpression), " ") + ")";
    }

    class SymbolicValue {
        constructor() {}

        eval() { return undefined; }
        visit(visitor) { visitor(this); }
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
            this.iid = J$.getGlobalIID(iid);
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

            visitor(this.left);
            if (this.left instanceof SymbolicValue) {
                this.left.visit(visitor);
            }

            visitor(this.right);
            if (this.right instanceof SymbolicValue) {
                this.right.visit(visitor);
            }
        }

        toFormula() {
            return ["js." + this.op, valueToFormula(this.left), valueToFormula(this.right)];
        }
    }

    class Unary extends SymbolicValue {
        constructor(iid, op, expr) {
            super();
            this.iid = J$.getGlobalIID(iid);
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
            visitor(this.expr);

            if (this.expr instanceof SymbolicValue) {
                this.expr.visit(visitor);
            }
        }

        toFormula() { return ["js." + this.op, valueToFormula(this.expr)]; }
    }

    function neg(iid, expr) {
        return new Unary(iid, "!", expr);
    }

    class SExprParser {
        constructor() {
            this._levels = [];
            this._curtok = null;
            this._parsingString = false;
            this._numQuotes = 0;
        }

        parse(str, cb) {
            for (let i = 0; i < str.length; ++i) {
                const expr = this._feedChar(str[i]);
                if (expr !== null && this._levels.length === 0) {
                    cb(expr);
                }
            }
        }

        _feedChar(char) {
            if (this._parsingString) {
                if (char === "\"") {
                    this._numQuotes++;

                    if (this._numQuotes >= 2) {
                        this._numQuotes -= 2;
                        this._curtok += "\"";
                    }

                    return null;
                } else {
                    if (this._numQuotes === 0) {
                        this._curtok += char;
                        return null;
                    } else if (this._numQuotes === 1) {
                        this._parsingString = false;
                        this._numQuotes = 0;
                        this._finishToken();
                    } else {
                        throw new Error("impossible");
                    }
                }
            }

            switch (char) {
                case "\r":
                case "\n":
                case "\t":
                case " ":
                    return this._finishToken();
                case "(":
                    this._levels.push([]);
                    break;
                case ")":
                    if (this._levels.length >= 1) {
                        this._finishToken();
                        const expr = this._levels.pop();
                        if (this._levels.length > 0) {
                            _.last(this._levels).push(expr);
                        } else {
                            return expr;
                        }
                    } else {
                        throw new Error("parse error: too many close-parens");
                    }
                    break;
                case "\"":
                    this._parsingString = true;
                    this._curtok = "";
                    break;
                default:
                    if (this._curtok === null) {
                        this._curtok = "";
                    }
                    this._curtok += char;
                    break;
            }

            return null;
        }

        _finishToken() {
            const token = this._curtok;
            if (token === null)
                return null;
            this._curtok = null;

            if (this._levels.length > 0) {
                _.last(this._levels).push(token);
                return null;
            } else {
                return token;
            }
        }
    }

    function collectVariables(expr) {
        const variables = {};
        expr.visit((expr) => {
            if (expr instanceof Variable) {
                variables[expr.name] = expr;
            }
        });
        return variables;
    }

    function generateSolverCommands(constraints) {
        const commands = [];
        const variables = {};

        for (let i = 0; i < constraints.length; ++i) {
            Object.assign(variables, collectVariables(constraints[i]));
        }

        _.forEach(variables, (v) => {
            commands.push(v.declarationFormula());
            if (!v.type.trivial()) {
                commands.push(["assert", v.type.constraintFor(v)]);
            }
        });

        for (let i = 0; i < constraints.length; ++i) {
            commands.push(["assert", constraints[i].toFormula()]);
        }

        commands.push(["check-sat"]);
        commands.push(["get-value", _.map(variables, (v) => v.toFormula())]);
        return commands;
    }

    const MAX_INPUTS = 10;
    const SOLVER_PATH = "../../z3/z3-4.5.0-x64-win/bin/z3";
    const ES_THEORY_PATH = "ecmascript.smt2";

    class Z3Solver extends EventEmitter {
        constructor() {
            super();

            const z3 = child_process.spawn(SOLVER_PATH, ["-smt2", "-in"]);
            z3.stdin.write(fs.readFileSync(ES_THEORY_PATH));

            z3.stdout.setEncoding("utf8");

            const parser = new SExprParser();
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
            const commandString = _.map(commands, stringifySExpression).join("\n");
            console.log(commandString);
            this.process.stdin.write(commandString);
        }

        close() {
            this.process.stdin.end("(exit)");
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
                addConstraint(value ? neg(iid, result) : result);
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

        invokeFunPre: function(iid, f, base, args) {
            if (f === sandbox.readInput) {
                return { f: f, base: base, args: args, skip: true };
            }
        },

        invokeFun: function(iid, f) {
            if (f === sandbox.readInput) {
                //var giid = J$.sid + "_" + iid;
                const giid = iid;
                return { result: new Variable("var" + giid, inputs[giid]) };
            }
        },

        onReady: function(cb) {
            const process = require("process");

            const solver = new Z3Solver();
            solver.on("output", (expr) => {
                console.log(expr);
            });

            function parseVarName(varName) {
                // Slice off the 'var' prefix.
                return varName.slice(3);
            }

            function parseVal(value) {
                const type = value[0],
                    contents = value[1];
                switch (type) {
                    case "Num":
                        return parseFloat(contents, 10);
                    default:
                        throw new Error("invalid value type " + type);
                }
            }

            function runAnalysis(n) {
                if (n <= 0) {
                    console.log("finished: reached iteration limit");
                    solver.close();
                    return;
                }

                constraints.length = 0;
                cb();

                // Delete the cached copy of the script so it can be reloaded.
                const input_filename = process.argv[1];
                delete require.cache[require.resolve(input_filename)];

                if (constraints.length === 0) {
                    console.log("finished: no more constraints to solve");
                    solver.close();
                    return;
                }

                const commands = generateSolverCommands(constraints);

                solver.push(1);
                solver.submitCommands(commands);
                solver.pop(1);

                solver.once("output", (expr) => {
                    if (expr === "sat") {
                        solver.once("output", (expr) => {
                            for (let j = 0; j < expr.length; j++) {
                                const name = expr[j][0],
                                    value = expr[j][1];
                                inputs[parseVarName(name)] = parseVal(value);
                            }

                            runAnalysis(n - 1);
                        });
                    } else if (expr === "unsat") {
                        // Absorb the error message from the (get-value) command
                        // before looping to test again.
                        solver.once("output", () => runAnalysis(n - 1));
                    } else {
                        throw new Error(`got ${expr} instead of sat or unsat`);
                    }
                });
            }

            runAnalysis(MAX_INPUTS);
        }
    };

    sandbox.readInput = function() {
        throw new Error("invalid call of readInput");
    };

})(J$);
