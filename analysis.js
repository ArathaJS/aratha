(function(sandbox) {
    "use strict";

    var util = require('util');
    var child_process = require('child_process');
    var _ = require('lodash');
    const EventEmitter = require('events');
    const fs = require('fs');

    var branches = {};
    var inputs = {};
    var constraints = [];

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

    function SymbolicValue() {
    }

    SymbolicValue.prototype.eval = function() {
        return undefined;
    }

    SymbolicValue.prototype.visit = function(visitor) {
        visitor(this);
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
                    return ["Num", value.toFixed(19)]
                } else {
                    return ["Num", ["-", (-value).toFixed(19)]];
                }
            case "string":
                return ["Str", escapeSMTString(value)];
            default:
                throw new Error("values of type " + typeof value + " not implemented");
        }
}

    function Type(types) {
        if (typeof types === "undefined") {
            types = Type.TOP;
        }

        this.types = types;
    }
    Type.prototype.constructor = Type;

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

    Type.prototype.requireTypes = function(types) {
        this.types &= types;
    }

    Type.prototype.forbidTypes = function(types) {
        this.types &= ~types;
    }

    Type.prototype.intersection = function(type) {
        return new Type(this.types & type.types);
    }

    Type.prototype.valid = function() {
        return this.types !== Type.BOTTOM;
    }

    Type.prototype.trivial = function() {
        return this.types === Type.TOP;
    }

    Type.prototype.has = function(types) {
        return (this.types & types) !== Type.BOTTOM;
    }

/*    Type.prototype.constraintFor = function(value) {
        var valFormula = valueToFormula(value),
            positive = [], negative = [];

        var predicates = this.predicates;

        for (var k in predicates) {
            if (predicates.hasOwnProperty(k)) {
                if (this.has(k)) {
                    positive.push(predicates[k]);
                } else {
                    negative.push(predicates[k]);
                }
            }
        }

        var positiveFormula = _.map(positive, function(x) { return [x, valFormula] });
        positiveFormula.unshift("or");

        var negativeFormula = _.map(negative, function(x) { return [x, valFormula]});
        negativeFormula.unshift("or");

        return ["and", positiveFormula, ["not", negativeFormula]];
    }
*/

    Type.prototype.constraintFor = function(value) {
        var valFormula = valueToFormula(value),
            negative = [];

        var predicates = Type.predicates;

        for (var k in predicates) {
            if (predicates.hasOwnProperty(k)) {
                if (!this.has(k)) {
                    negative.push(predicates[k]);
                }
            }
        }

        if (negative.length > 0) {
            var negativeFormula = _.map(negative, function(x) { return [x, valFormula]});
            negativeFormula.unshift("or");
            return ["not", negativeFormula];
        } else {
            return "true";
        }
    }

    function Variable(name, concreteValue, type) {
        this.name = name;
        this.concreteValue = concreteValue;
        this.type = type || new Type();
    }
    Variable.prototype = Object.create(SymbolicValue.prototype);
    Variable.prototype.constructor = Variable;

    Variable.prototype.eval = function() {
        return this.concreteValue;
    }

    Variable.prototype.toFormula = function() {
        return this.name;
    }

    Variable.prototype.declarationFormula = function() {
        return ["declare-const", this.name, "Val"];
    }

    function neg(iid, expr)
    {
        return new Unary(iid, '!', expr);
    }

    function Binary(iid, op, left, right) {
        this.iid = J$.getGlobalIID(iid);
        this.op = op;
        this.left = left;
        this.right = right;
    }
    Binary.prototype = Object.create(SymbolicValue.prototype);
    Binary.prototype.constructor = Binary;

    Binary.prototype.eval = function() {
        var op = this.op,
            left = this.left,
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
                break;
        }

        return result;
    }

    Binary.prototype.visit = function(visitor) {
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

    Binary.prototype.toFormula = function() {
        return ["js." + this.op, valueToFormula(this.left), valueToFormula(this.right)];
    }

    function Unary(iid, op, expr) {
        this.iid = J$.getGlobalIID(iid);
        this.op = op;
        this.expr = expr;
    }
    Unary.prototype = Object.create(SymbolicValue.prototype);
    Unary.prototype.constructor = Unary;

    Unary.prototype.eval = function() {
        var expr = this.expr,
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
                break;
        }

        return result;
    }

    Unary.prototype.visit = function(visitor) {
        visitor(this);
        visitor(this.expr);

        if (this.expr instanceof SymbolicValue) {
            this.expr.visit(visitor);
        }
    }

    Unary.prototype.toFormula = function() {
        return ["js." + this.op, valueToFormula(this.expr)];
    }

    class SExprParser {
        constructor() {
            this._levels = [];
            this._curtok = null;
            this._parsingString = false;
            this._numQuotes = 0;
        }

        parse(str, cb) {
            for(let i = 0; i < str.length; ++i) {
                let expr = this._feedChar(str[i]);
                if (expr !== null && this._levels.length === 0) {
                    cb(expr);
                }
            }
        }

        _feedChar(char) {
            if (this._parsingString) {
                if (char === '"') {
                    this._numQuotes++;

                    if (this._numQuotes >= 2) {
                        this._numQuotes -= 2;
                        this._curtok += '"';
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

            switch(char) {
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
                        let expr = this._levels.pop();
                        if (this._levels.length > 0) {
                            _.last(this._levels).push(expr);
                        } else {
                            return expr;
                        }
                    } else {
                        throw new Error("parse error: too many close-parens");
                    }
                    break;
                case '"':
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
            let token = this._curtok;
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
        var variables = {};
        expr.visit(function(expr) {
            if(expr instanceof Variable) {
                variables[expr.name] = expr;
            }
        });
        return variables;
    }

    function generateSolverCommands(constraints) {
        var commands = [];
        var variables = {};

        for (var i = 0; i < constraints.length; ++i) {
            Object.assign(variables, collectVariables(constraints[i]));
        }

        _.forEach(variables, function(v) {
            commands.push(v.declarationFormula());
            if (!v.type.trivial()) {
                commands.push(["assert", v.type.constraintFor(v)]);
            }
        });

        for (var i = 0; i < constraints.length; ++i) {
            commands.push(["assert", constraints[i].toFormula()]);
        }

        commands.push(["check-sat"]);
        commands.push(["get-value", _.map(variables, function(v) { return v.toFormula(); })]);
        return commands;
    }

    const MAX_INPUTS = 10;
    const SOLVER_PATH = '../../z3/z3-4.5.0-x64-win/bin/z3';
    const ES_THEORY_PATH = 'ecmascript.smt2';

    class Z3Solver extends EventEmitter {
        constructor() {
            super();

            let z3 = child_process.spawn(SOLVER_PATH, ['-smt2', '-in']);
            z3.stdin.write(fs.readFileSync(ES_THEORY_PATH));

            z3.stdout.setEncoding('utf8');

            let parser = new SExprParser();
            z3.stdout.on('data', (data) => {
                parser.parse(data, (expr) => {
                    this.emit('output', expr);
                });
            });

            this.process = z3;
        }

        push(n) {
            this.submitCommands([["push", n.toString()]]);
        }

        pop(n) {
            this.submitCommands([["pop", n.toString()]]);
        }

        submitCommands(commands) {
            var commandString = _.map(commands, stringifySExpression).join("\n");
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
     conditional : function (iid, result) {
        if (result instanceof SymbolicValue) {
            var value = result.eval();
            addConstraint(value ? neg(iid, result) : result);
            return {result: value};
        }
    },

    binaryPre: function (iid, op, left, right, isOpAssign, isSwitchCaseComparison, isComputed) {
        if ((left instanceof SymbolicValue) || (right instanceof SymbolicValue)) {
            return {op: op, left: left, right: right, skip: true};
        }
    },

    binary: function (iid, op, left, right, result, isOpAssign, isSwitchCaseComparison, isComputed) {
        if ((left instanceof SymbolicValue) || (right instanceof SymbolicValue)) {
            return {result: new Binary(iid, op, left, right)};
        }
    },

    invokeFunPre: function (iid, f, base, args, isConstructor, isMethod, functionIid, functionSid) {
        if (f === sandbox.readInput) {
            return {skip: true, f: f, base: base, args: args};
        }
    },

    invokeFun: function (iid, f, base, args, result, isConstructor, isMethod, functionIid, functionSid) {
        if (f === sandbox.readInput) {
            //var giid = J$.sid + "_" + iid;
            var giid = iid;
            return {result: new Variable("var" + giid, inputs[giid])};
        }
    },

    onReady: function(cb) {
        var input_filename = './example.js';
        var solver = new Z3Solver();
        solver.on('output', function(expr) {
            console.log(expr);
        });

        function parseVarName(varName) {
            // Slice off the 'var' prefix.
            return varName.slice(3);
        }

        function parseVal(value) {
            let type = value[0], contents = value[1];
            switch(type) {
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

            delete require.cache[require.resolve(input_filename)];
            constraints.length = 0;
            cb();

            if (constraints.length === 0) {
                console.log("finished: no more constraints to solve");
                solver.close();
                return;
            }

            let commands = generateSolverCommands(constraints);

            solver.push(1)
            solver.submitCommands(commands);
            solver.pop(1);

            solver.once('output', (expr) => {
                if (expr === 'sat') {
                    solver.once('output', (expr) => {
                        for(let j = 0; j < expr.length; j++) {
                            let name = expr[j][0], value = expr[j][1];
                            inputs[parseVarName(name)] = parseVal(value);
                        }

                        runAnalysis(n - 1);
                    });
                } else if (expr === 'unsat') {
                    // Absorb the error message from the (get-value) command
                    // before looping to test again.
                    solver.once('output', () => runAnalysis(n - 1));
                } else {
                    throw new Error(`got ${expr} instead of sat or unsat`);
                }
            });
        }

        runAnalysis(MAX_INPUTS);
    }
};

sandbox.readInput = function(concreteValue) {
    throw new Error("invalid call of readInput");
};

}(J$));
