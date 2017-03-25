"use strict";

const Type = require("./type");

class SymbolicValue {
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
            return ["Str", '"' + value.replace('"', '""') + '"'];
        default:
            throw new Error("values of type " + typeof value + " not implemented");
    }
}

exports.SymbolicValue = SymbolicValue;

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

exports.Variable = Variable;

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
        let name = this.op;
        if (name === "|")
            name = "bitor";
        return ["js." + name, valueToFormula(this.left), valueToFormula(this.right)];
    }
}

exports.Binary = Binary;

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

    toFormula() {
        let name = this.op;
        if (name === "+" || name === "-")
            name = "u" + name;
        return ["js." + name, valueToFormula(this.expr)];
    }
}

exports.Unary = Unary;

class GetField extends SymbolicValue {
    constructor(iid, base, offset, concreteValue) {
        super();
        this.iid = iid;
        this.base = base;
        this.offset = offset;
        this.concreteValue = concreteValue;
    }

    eval() {
        return this.concreteValue;
    }

    visit(visitor) {
        visitor(this);
        this._visitChild(this.base, visitor);
        this._visitChild(this.offset, visitor);
    }

    toFormula() {
        return ["js.GetField", valueToFormula(this.base), valueToFormula(this.offset)];
    }
}

exports.GetField = GetField;
