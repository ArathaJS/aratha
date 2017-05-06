"use strict";

const _ = require("lodash");

const { doBinaryOp, doUnaryOp } = require("./ops");

class SymbolicValue {
    visit(visitor) { visitor(this); }

    _visitChild(child, visitor) {
        if (child instanceof SymbolicValue) {
            child.visit(visitor);
        } else {
            visitor(child);
        }
    }

    toObjectFormula() {
        return ["js.ToObject", this.toFormula()];
    }
}

function isDistinct(a, b) {
    if (!_.isObject(a) && !_.isObject(b)) {
        return a !== b;
    }

    return false;
}

exports.SymbolicValue = SymbolicValue;

class Variable extends SymbolicValue {
    constructor(name) {
        super();
        this.name = name;
    }

    eval(model) {
        return model[this.name];
    }

    toFormula() { return this.name; }

    toString() { return this.name; }
}

exports.Variable = Variable;

function escapeString(s) { return '"' + s.replace('"', '""') + '"'; }

function primitiveToFormula(v) {
    switch (typeof v) {
        case "undefined":
            return "undefined";
        case "null":
            return "null";
        case "boolean":
            return ["Boolean", v.toString()];
        case "number":
            if (v >= 0) {
                return ["Num", v.toFixed(19)];
            } else {
                return ["Num", ["-", (-v).toFixed(19)]];
            }
        case "string":
            return ["Str", escapeString(v)];
        default:
            throw new Error("type " + typeof v + " is not primitive");
    }
}

class Constant extends SymbolicValue {
    constructor(value) {
        super();
        if (_.isObject(value)) {
            value = _.clone(value);
        }
        this.value = value;
    }

    eval() { return this.value; }

    toFormula() { return primitiveToFormula(this.value); }

    toObjectFormula() {
        if (!_.isObject(this.value)) {
            return ["js.ToObject", this.toFormula()];
        }

        let result = "EmptyObject";
        const o = this.value;
        for (const k in o) {
            if (o.hasOwnProperty(k)) {
                result = ["store", result, escapeString(k), primitiveToFormula(o[k])];
            }
        }
        return result;
    }
}

exports.Constant = Constant;

class Binary extends SymbolicValue {
    constructor(op, left, right) {
        super();
        this.op = op;
        this.left = left;
        this.right = right;
    }

    eval(model) {
        return doBinaryOp(this.op, this.left.eval(model), this.right.eval(model));
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
        return ["js." + name, this.left.toFormula(), this.right.toFormula()];
    }

    toString() { return `(${this.left} ${this.op} ${this.right})`; }
}

exports.Binary = Binary;

class Unary extends SymbolicValue {
    constructor(op, expr) {
        super();
        this.op = op;
        this.expr = expr;
    }

    visit(visitor) {
        visitor(this);
        this._visitChild(this.expr, visitor);
    }

    eval(model) {
        return doUnaryOp(this.op, this.expr.eval(model));
    }

    toFormula() {
        let name = this.op;
        if (name === "+" || name === "-")
            name = "u" + name;
        return ["js." + name, this.expr.toFormula()];
    }

    toString() { return `(${this.op} ${this.expr})`; }
}

exports.Unary = Unary;

class ObjectOp extends SymbolicValue {
    getTopBase() {
        let node = this;
        while (node instanceof ObjectOp) {
            node = node.base;
        }
        return node;
    }
}

class PutField extends ObjectOp {
    constructor(base, offset, val) {
        super();
        this.base = base;
        this.offset = offset;
        this.val = val;
    }

    visit(visitor) {
        visitor(this);
        this._visitChild(this.base, visitor);
        this._visitChild(this.offset, visitor);
        this._visitChild(this.val, visitor);
    }

    eval(model) { return this.base.eval(model); }

    toObjectFormula() {
        return ["PutField", this.base.toObjectFormula(), this.offset.toFormula(), this.val.toFormula()];
    }

    toFormula() { return this.base.toFormula(); }

    toString() { return this.base.toString(); }
}

exports.PutField = PutField;

class GetField extends ObjectOp {
    constructor(base, offset) {
        super();
        this.base = base;
        this.offset = offset;
    }

    eval(model) {
        const offset = String(this.offset.eval(model));

        let node = this.base;
        while (node instanceof PutField) {
            if (String(node.offset.eval(model)) === offset) {
                return node.val.eval(model);
            }

            node = node.base;
        }

        node = node.eval(model);

        return node[offset];
    }

    visit(visitor) {
        visitor(this);
        this._visitChild(this.base, visitor);
        this._visitChild(this.offset, visitor);
    }

    _simplify() {
        let node = this.base;
        while (node instanceof PutField) {
            if (_.isEqual(node.offset, this.offset)) {
                return node.val;
            }

            if (!isDistinct(node.offset, this.offset)) {
                break;
            }

            node = node.base;
        }
    }

    toFormula() {
        const resolved = this._simplify();
        if (resolved) {
            return resolved.toFormula();
        }

        let props = this.base.toObjectFormula();
        if (this.getTopBase() instanceof Variable) {
            // In case our base is a temporary, we need to add a dynamic
            // constraint: if the base is an object, return it with the
            // modifications applied. Otherwise, return the original base.
            props = ["MutableToProps", this.base.toFormula(), props];
        }

        return ["GetField", props, this.offset.toFormula()];
    }

    toString() { return `${this.base}[${this.offset}]`; }
}

exports.GetField = GetField;
