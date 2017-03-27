"use strict";

exports.doBinaryOp = function(op, left, right) {
    let result;
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
            throw new Error(op + " not found");
    }

    return result;
};

exports.doUnaryOp = function(op, left) {
    let result;
    switch (op) {
        case "+":
            result = +left;
            break;
        case "-":
            result = -left;
            break;
        case "~":
            result = ~left;
            break;
        case "!":
            result = !left;
            break;
        case "typeof":
            result = typeof left;
            break;
        case "void":
            result = void(left);
            break;
        default:
            throw new Error(op + " not found");
    }

    return result;
};
