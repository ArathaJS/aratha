(function(sandbox) {
    var branches = {};
    var stack = [];

    function addConstraint(val) {
        stack.push(val);
    }

    function SymbolicValue(iid) {
        this.iid = J$.getGlobalIID(iid);
    }

    SymbolicValue.prototype.eval = function() {
        return undefined;
    }

    function Variable(iid) {
        this.iid = J$.getGlobalIID(iid);
    }
    Variable.prototype = Object.create(SymbolicValue.prototype);
    Variable.constructor = Variable;

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

    function Unary(iid, op, expr) {
        this.iid = J$.getGlobalIID(iid);
        this.op = op;
        this.expr = expr;
    }
    Unary.prototype = Object.create(SymbolicValue.prototype);
    Unary.prototype.constructor = Unary;

    Unary.prototype.eval = function() {
        throw new Error("Not implemented yet");
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
        console.log(stack);
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

sandbox.readInput = function() {
    return new SymbolicValue();
}

}(J$));
