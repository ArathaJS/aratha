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

    toStringFormula() {
        return ["js.ToString", this.toFormula()];
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

let objectIdCounter = 0;
const objectIdMap = new WeakMap();

function getObjectId(o) {
    if (objectIdMap.has(o)) {
        return objectIdMap.get(o);
    }
    const id = objectIdCounter++;
    objectIdMap.set(o, id);
    return id;
}

class Constant extends SymbolicValue {
    constructor(value) {
        super();
        if (_.isObject(value)) {
            this.objectId = getObjectId(value);
            value = _.clone(value);
        }
        this.value = value;
    }

    eval() { return this.value; }

    toFormula() {
        const v = this.value;
        if (_.isObject(v)) {
            return ["Obj", this.objectId.toString()];
        } else {
            return primitiveToFormula(v);
        }
    }

    toObjectFormula() {
        if (!_.isObject(this.value)) {
            return ["js.ToObject", primitiveToFormula(this.value)];
        }

        let result = "EmptyObject";
        const o = this.value;
        for (const k in o) {
            if (o.hasOwnProperty(k)) {
                let v = o[k];
                if (_.isObject(v)) {
                    v = ["Obj", getObjectId(v)];
                } else {
                    v = primitiveToFormula(v);
                }
                v = ["Just", v];
                result = ["store", result, escapeString(k), v];
            }
        }
        return result;
    }

    toStringFormula() {
        return escapeString(String(this.value));
    }
}

exports.Constant = Constant;


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

class DeleteField extends ObjectOp {
    constructor(base, offset) {
        super();
        this.base = base;
        this.offset = offset;
    }

    visit(visitor) {
        visitor(this);
        this._visitChild(this.base, visitor);
        this._visitChild(this.offset, visitor);
    }

    eval(model) { return this.base.eval(model); }

    toObjectFormula() {
        return ["DeleteField", this.base.toObjectFormula(), this.offset.toFormula()];
    }

    toFormula() { return this.base.toFormula(); }

    toString() { return this.base.toString(); }
}

exports.DeleteField = DeleteField;

class GetField extends ObjectOp {
    constructor(base, offset) {
        super();
        this.base = base;
        this.offset = offset;
    }

    eval(model) {
        const offset = String(this.offset.eval(model));

        let node = this.base;
        while (node instanceof PutField || node instanceof DeleteField) {
            const nodeOffset = String(node.offset.eval(model));
            if (nodeOffset === offset) {
                if (node instanceof PutField) {
                    return node.val.eval(model);
                } else {
                    // Field was deleted, return undefined.
                    return undefined;
                }
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

    static simplify(base, offset) {
        let node = base;
        while (node instanceof PutField || node instanceof DeleteField) {
            if (_.isEqual(node.offset, offset)) {
                if (node instanceof PutField) {
                    return {result: node.val};
                } else {
                    return {result: undefined};
                }
            }

            if (!isDistinct(node.offset, offset)) {
                return null;
            }

            node = node.base;
        }

        if (node instanceof Constant && offset instanceof Constant) {
            return node.value[offset.value];
        }

        return null;
    }

    toFormula() {
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

class Binary extends SymbolicValue {
    constructor(op, left, right) {
        super();
        this.op = op;
        this.left = left;
        this.right = right;
    }

    eval(model) {
        if (this.op === "in")
            return this._evalIn(model);

        return doBinaryOp(this.op, this.left.eval(model), this.right.eval(model));
    }

    _evalIn(model) {
        const key = String(this.left.eval(model));
        let node = this.right;
        while (node instanceof PutField || node instanceof DeleteField) {
            const nodeOffset = String(node.offset.eval(model));
            if (nodeOffset === key) {
                if (node instanceof PutField) {
                    return true;
                } else {
                    // Field was deleted, return false.
                    return false;
                }
            }

            node = node.base;
        }

        node = node.eval(model);
        return key in node;
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
        if (name === "in") {
            return ["js.in", this.left.toFormula(), this.right.toObjectFormula()];
        }
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

class StringConcat extends SymbolicValue {
    constructor(base, args) {
        super();
        this.base = base;
        this.args = args;
    }

    visit(visitor) {
        visitor(this);
        this._visitChild(this.base, visitor);
        for (let i = 0; i < this.args.length; i++) {
            this._visitChild(this.args[i], visitor);
        }
    }

    eval(model) {
        const evaluatedArgs = _.map(this.args, (a) => a.eval(model));
        return String.prototype.concat.apply(this.base.eval(model), evaluatedArgs);
    }

    toStringFormula() {
        const formula = ["str.++", this.base.toStringFormula()];
        for (let i = 0; i < this.args.length; i++) {
            formula.push(this.args[i].toStringFormula());
        }
        return formula;
    }

    toFormula() {
        return ["Str", this.toStringFormula()];
    }
}
exports.StringConcat = StringConcat;
