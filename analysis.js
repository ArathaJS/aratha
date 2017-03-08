(function(sandbox) {
    var util = require('util');
    var _ = require('lodash');

    var branches = {};
    var constraints = [];
    var varNameCounter = 0;

    function addConstraint(val) {
        if (!_.some(constraints, _.partial(_.isEqual, val))) {
            constraints.push(val);
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

     /**
      * This callback is called when an execution terminates in node.js.  In a browser
      * environment, the callback is called if ChainedAnalyses.js or ChainedAnalysesNoCheck.js
      * is used and Alt-Shift-T is pressed.
      *
      * @returns {undefined} - Any return value is ignored
      */
      endExecution : function () {
        // console.log(util.inspect(constraints, false, null));
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


        for (var i = 0; i < commands.length; ++i) {
            console.log(stringifySExpression(commands[i]));
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
    }
};

sandbox.readInput = function(concreteValue) {
    return new Variable("var" + varNameCounter++, concreteValue);
};

}(J$));
