"use strict";

const _ = require("lodash");

const { doBinaryOp, doUnaryOp } = require("./ops");
const { escapeString } = require("./smtlib");
const Type = require("./type");

class SymbolicValue {
    visit(visitor) { visitor(this); }

    _visitChild(child, visitor) {
        if (child instanceof SymbolicValue) {
            child.visit(visitor);
        } else {
            visitor(child);
        }
    }

    getConstraints() { return []; }

    toObjectFormula() {
        if (this.getType() === Type.STRING) {
            return ["StringToObject", this.toStringFormula()];
        }

        return ["js.ToObject", this.toFormula()];
    }

    toStringFormula() {
        return ["js.ToString", this.toFormula()];
    }

    toIntegerFormula() {
        return ["js.ToInteger", this.toFormula()];
    }

    toBooleanFormula() {
        if (this.getType() === Type.STRING) {
            return ["distinct", this.toStringFormula(), '""'];
        }

        return ["js.ToBoolean", this.toFormula()];
    }

    getType() {
        return Type.TOP;
    }

    toNativeFormula() {
        switch (this.getType()) {
            case Type.UNDEFINED:
                return "undefined";
            case Type.NULL:
                return "null";
            case Type.STRING:
                return this.toStringFormula();
            case Type.NUMBER:
                return this.toIntegerFormula();
            case Type.BOOLEAN:
                return this.toBooleanFormula();
            case Type.OBJECT:
                return this.toObjectFormula();
            default:
                return this.toFormula();
        }
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
    constructor(name, type) {
        super();
        this.name = name;
        this.type = type;
    }

    eval(model) {
        return model[this.name];
    }

    getType() {
        return this.type;
    }

    toObjectFormula() {
        if (this.type === Type.OBJECT)
            return ["GetProperties", ["id", this.toFormula()]];
        else
            return super.toObjectFormula();
    }

    toStringFormula() {
        if (this.type === Type.STRING)
            return ["str", this.toFormula()];
        else
            return super.toStringFormula();
    }

    toIntegerFormula() {
        if (this.type === Type.NUMBER)
            return ["num", this.toFormula()];
        else
            return super.toIntegerFormula();
    }

    toBooleanFormula() {
        if (this.type === Type.BOOLEAN)
            return ["bool", this.toFormula()];
        else
            return super.toBooleanFormula();
    }

    toFormula() { return this.name; }

    toString() { return this.name; }

}

exports.Variable = Variable;

function primitiveToFormula(v) {
    if (v === null) {
        return "null";
    }
    switch (typeof v) {
        case "undefined":
            return v;
        case "boolean":
            return ["Boolean", v];
        case "number":
            return ["Num", v];
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

function ToInteger(v) {
    v = Number(v);
    if (Number.isNaN(v))
        return +0;
    const c = Math.abs(Math.floor(v));
    return v >= 0 ? c : -c;
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
                    v = ["Obj", getObjectId(v).toString()];
                } else {
                    v = primitiveToFormula(v);
                }
                v = ["Just", v];
//                console.log("storing", o, k, v);
                result = ["store", result, escapeString(k), v];
            }
        }
//        console.log("result", result);
        return result;
    }

    toStringFormula() {
        return escapeString(String(this.value));
    }

    toIntegerFormula() {
        const val = ToInteger(this.value);
        return val >= 0 ? val.toString() : ["-", (-val).toString()];
    }

    toBooleanFormula() {
        return Boolean(this.value).toString();
    }

    getType() {
        switch(typeof this.value) {
            case "undefined":
                return Type.UNDEFINED;
            case "boolean":
                return Type.BOOLEAN;
            case "number":
                return Type.NUMBER;
            case "string":
                return Type.STRING;
            case "object":
                return this.value === null ? Type.NULL : Type.OBJECT;
            default:
                return Type.TOP;
        }
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
        const topBase = this.getTopBase().eval(model);
        if (typeof topBase !== "object" || topBase === "null") {
            return topBase[this.offset.eval(model)];
        }

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
        if (base.getType() !== Type.OBJECT) {
            return null;
        }
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

    getType() {
        if (!(this.base instanceof ObjectOp) && this.base.getType() === Type.STRING && this.offset instanceof Constant && this.offset.value === "length") {
            return Type.NUMBER;
        }

        if (!(this.base instanceof ObjectOp) && this.base.getType() === Type.STRING && this.offset.getType() === Type.NUMBER) {
            return Type.STRING;
        }

        return super.getType();
    }

    toIntegerFormula() {
        if (!(this.base instanceof ObjectOp) && this.base.getType() === Type.STRING && this.offset instanceof Constant && this.offset.value === "length") {
            return ["str.len", this.base.toStringFormula()];
        }
        return super.toIntegerFormula();
    }

    toStringFormula() {
        if (!(this.base instanceof ObjectOp) && this.base.getType() === Type.STRING && this.offset.getType() === Type.NUMBER) {
            return ["str.at", this.base.toStringFormula(), this.offset.toIntegerFormula()];
        }
        return super.toStringFormula();
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

    getType() {
        let type = Type.TOP;
        switch(this.op) {
            case "===":
            case "!==":
            case "==":
            case "!=":
            case ">=":
            case "<=":
            case ">":
            case "<":
            case "in":
            case "instanceof":
            case "delete":
                type = Type.BOOLEAN;
                break;
            case "-":
            case "*":
            case "/":
            case "%":
            case "<<":
            case ">>":
            case ">>>":
            case "&":
            case "|":
            case "^":
                type = Type.NUMBER;
                break;
            case "+": {
                const ltype = this.left.getType();
                const rtype = this.right.getType();
                if (ltype === Type.STRING || rtype === Type.STRING) {
                    type = Type.STRING;
                } else if (!(ltype & Type.STRING) && !(rtype & Type.STRING)) {
                    type = Type.NUMBER;
                } else {
                    type = Type.NUMBER | Type.STRING;
                }
            }
        }
        return type;
    }

    toIntegerFormula() {
        let op = this.op;
        if (op === "%") {
            op = "mod";
        }
        if (op === "/") {
            op = "div";
        }
        if (op === "&") {
            op = "IntAnd32";
        }
        if (op === "|") {
            op = "IntOr32";
        }
        if (op === "^") {
            op = "IntXor32";
        }

        switch (op) {
            case "-":
            case "*":
            case "div":
            case "mod":
            case "IntAnd32":
            case "IntOr32":
            case "IntXor32": {
                const left = this.left.toIntegerFormula();
                const right = this.right.toIntegerFormula();
                return [op, left, right];
            }
            case "+": {
                if (this.getType() === Type.NUMBER) {
                    const left = this.left.toIntegerFormula();
                    const right = this.right.toIntegerFormula();
                    return [op, left, right];
                }
            }
        }

        return super.toIntegerFormula();
    }

    toBooleanFormula() {
        const op = this.op;

        if (op === "===" || op === "==") {
            const ltype = new Type(this.left.getType());
            const rtype = new Type(this.right.getType());
            if (ltype.isSingleton() && rtype.isSingleton()) {
                if (ltype.isEqual(rtype)) {
                    return ["=", this.left.toNativeFormula(), this.right.toNativeFormula()];
                } else {
                    return "false";
                }
            }
        }

        if (op === "!==" || op === "!=") {
            const ltype = new Type(this.left.getType());
            const rtype = new Type(this.right.getType());
            if (ltype.isSingleton() && rtype.isSingleton()) {
                if (ltype.isEqual(rtype)) {
                    return ["distinct", this.left.toNativeFormula(), this.right.toNativeFormula()];
                } else {
                    return "true";
                }
            }
        }


        if (this.left.getType() === Type.NUMBER && this.right.getType() === Type.NUMBER) {
            switch(op) {
                case ">=":
                case "<=":
                case ">":
                case "<":
                    return [op, this.left.toIntegerFormula(), this.right.toIntegerFormula()];
            }
        }

        if (this.getType() === Type.NUMBER) {
            return ["distinct", this.toIntegerFormula(), 0];
        }

        switch(op) {
            case "===":
            case "!==":
            case "==":
            case "!=":
            case ">=":
            case "<=":
            case ">":
            case "<":
            case "instanceof":
                return ["js." + op, this.left.toFormula(), this.right.toFormula()];
            case "in":
                return ["js.in", this.left.toStringFormula(), this.right.toObjectFormula()];
            default:
                return super.toBooleanFormula();
        }
    }

    toStringFormula() {
        if (this.getType() === Type.STRING) {
            return ["str.++", this.left.toStringFormula(), this.right.toStringFormula()];
        }

        return super.toStringFormula();
    }

    toFormula() {
        let name = this.op;
        switch (name) {
            case "+": {
                if (this.getType() == Type.NUMBER) {
                    return ["Num", this.toIntegerFormula()];
                }
                break;
            }
            case "-":
            case "*":
            case "/":
            case "%": {
                return ["Num", this.toIntegerFormula()];
            }
            case "===":
            case "!==":
            case "==":
            case "!=":
            case ">=":
            case "<=":
            case ">":
            case "<":
            case "in": {
                return ["Boolean", this.toBooleanFormula()];
            }
            case "|":
                name = "bitor";
                break;
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

    getType() {
        switch(this.op) {
            case "!":
                return Type.BOOLEAN;
            case "~":
            case "-":
            case "+":
                return Type.NUMBER;
            case "typeof":
                return Type.STRING;
            case "void":
                return Type.UNDEFINED;
            default:
                return Type.TOP;
        }
    }

    toBooleanFormula() {
        if (this.op === "!") {
            return ["not", this.expr.toBooleanFormula()];
        }
        return super.toBooleanFormula();
    }

    toIntegerFormula() {
        switch (this.op) {
            case "~":
                return ["num", ["js.~", this.expr.toFormula()]];
            case "-":
                return ["-", this.expr.toIntegerFormula()];
            case "+":
                return this.expr.toIntegerFormula();
            default:
                return super.toIntegerFormula();
        }
    }

    toStringFormula() {
        if (this.op === "typeof") {
            return ["str", ["js.typeof", this.expr.toFormula()]];
        }
        return super.toStringFormula();
    }

    toFormula() {
        let name = this.op;
        if (name === "!") {
            return ["Boolean", this.toBooleanFormula()];
        }
        if (name === "+" || name === "-")
            name = "u" + name;
        return ["js." + name, this.expr.toFormula()];
    }

    toString() { return `(${this.op} ${this.expr})`; }
}

exports.Unary = Unary;


class StringToString extends SymbolicValue {
    constructor(base) {
        super();
        this.base = base;
    }

    visit(visitor) {
        visitor(this);
        this._visitChild(this.base, visitor);
    }

    eval(model) {
        return String.prototype.toString.call(this.base.eval(model));
    }

    toStringFormula() {
        return this.base.toStringFormula();
    }

    getType() {
        return Type.STRING;
    }

    toFormula() {
        return ["Str", this.toStringFormula()];
    }
}
exports.StringToString = StringToString;

class StringConcat extends SymbolicValue {
    constructor(base, ...args) {
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

    getType() {
        return Type.STRING;
    }

    toFormula() {
        return ["Str", this.toStringFormula()];
    }
}
exports.StringConcat = StringConcat;

class StringCharAt extends SymbolicValue {
    constructor(base, idx) {
        super();
        this.base = base;
        this.idx = idx;
    }

    visit(visitor) {
        visitor(this);
        this._visitChild(this.base, visitor);
        this._visitChild(this.idx, visitor);
    }

    eval(model) {
        return String.prototype.charAt.call(this.base.eval(model), this.idx.eval(model));
    }

    toStringFormula() {
        return ["str.at", this.base.toStringFormula(), this.idx.toIntegerFormula()];
    }

    getType() {
        return Type.STRING;
    }

    toFormula() {
        return ["Str", this.toStringFormula()];
    }
}
exports.StringCharAt = StringCharAt;

class StringRepeat extends SymbolicValue {
    constructor(base, num) {
        super();
        this.base = base;
        this.num = num;
    }

    visit(visitor) {
        visitor(this);
        this._visitChild(this.base, visitor);
        this._visitChild(this.num, visitor);
    }

    eval(model) {
        return String.prototype.repeat.call(this.base.eval(model), this.num.eval(model));
    }

    toStringFormula() {
        const n = this.num.toIntegerFormula();
        return ["re.to.str", ["re.loop", ["str.to.re", this.base.toStringFormula()], n, n]];
    }

    getType() {
        return Type.STRING;
    }

    toFormula() {
        return ["Str", this.toStringFormula()];
    }
}
exports.StringRepeat = StringRepeat;

class StringSubstr extends SymbolicValue {
    constructor(base, start, len=new Constant(undefined)) {
        super();
        this.base = base;
        this.start = start;
        this.len = len;
    }

    visit(visitor) {
        visitor(this);
        this._visitChild(this.base, visitor);
        this._visitChild(this.start, visitor);
        this._visitChild(this.len, visitor);
    }

    eval(model) {
        return String.prototype.substring.call(this.base.eval(model), this.start.eval(model), this.len.eval(model));
    }

    toStringFormula() {
        return ["js.substr", this.base.toStringFormula(), this.start.toIntegerFormula(), this.len.toFormula()];
    }

    getType() {
        return Type.STRING;
    }

    toFormula() {
        return ["Str", this.toStringFormula()];
    }
}
exports.StringSubstr = StringSubstr;

class StringSubstring extends SymbolicValue {
    constructor(base, start, end=new Constant(undefined)) {
        super();
        this.base = base;
        this.start = start;
        this.end = end;
    }

    visit(visitor) {
        visitor(this);
        this._visitChild(this.base, visitor);
        this._visitChild(this.start, visitor);
        this._visitChild(this.end, visitor);
    }

    eval(model) {
        return String.prototype.substring.call(this.base.eval(model), this.start.eval(model), this.end.eval(model));
    }

    toStringFormula() {
        return ["js.substring", this.base.toStringFormula(), this.start.toIntegerFormula(), this.end.toFormula()];
    }

    getType() {
        return Type.STRING;
    }

    toFormula() {
        return ["Str", this.toStringFormula()];
    }
}
exports.StringSubstring = StringSubstring;

class StringSlice extends SymbolicValue {
    constructor(base, start, end=new Constant(undefined)) {
        super();
        this.base = base;
        this.start = start;
        this.end = end;
    }

    visit(visitor) {
        visitor(this);
        this._visitChild(this.base, visitor);
        this._visitChild(this.start, visitor);
        this._visitChild(this.end, visitor);
    }

    eval(model) {
        return String.prototype.slice.call(this.base.eval(model), this.start.eval(model), this.end.eval(model));
    }

    toStringFormula() {
        return ["js.slice", this.base.toStringFormula(), this.start.toIntegerFormula(), this.end.toFormula()];
    }

    getType() {
        return Type.STRING;
    }

    toFormula() {
        return ["Str", this.toStringFormula()];
    }
}
exports.StringSlice = StringSlice;

class StringSplit extends SymbolicValue {
    constructor(base, sep, len = new Constant(2)) { // FIXME: the limit, len, is not default 2, but unbounded.
        super();
        this.base = base;
        this.sep = sep;
        this.len = len;
    }

    visit(visitor) {
        visitor(this);
        this._visitChild(this.base, visitor);
        this._visitChild(this.sep, visitor);
        this._visitChild(this.len, visitor);
    }

    eval(model) {
        return String.prototype.split.call(
            this.base.eval(model), this.sep.eval(model), this.len.eval(model)
        );
    }

    toObjectFormula() {
        return ["js.split", this.base.toStringFormula(),
            this.sep.toStringFormula(), this.len.toIntegerFormula()];
    }

    getType() {
        return Type.OBJECT;
    }

    toFormula() {
        return ["Obj", this.toObjectFormula()];
    }

}
exports.StringSplit = StringSplit;

class StringIndexOf extends SymbolicValue {
    constructor(base, searchString, offset) {
        super();
        this.base = base;
        this.searchString = searchString;
        this.offset = offset || new Constant(0);
    }

    visit(visitor) {
        visitor(this);
        this._visitChild(this.base, visitor);
        this._visitChild(this.searchString, visitor);
        this._visitChild(this.offset, visitor);
    }

    eval(model) {
        return String.prototype.indexOf.call(this.base.eval(model), this.searchString.eval(model), this.offset.eval(model));
    }

    toIntegerFormula() {
        return ["str.indexof", this.base.toStringFormula(), this.searchString.toStringFormula(), this.offset.toIntegerFormula()];
    }

    getType() {
        return Type.NUMBER;
    }

    toFormula() {
        return ["Num", this.toIntegerFormula()];
    }
}
exports.StringIndexOf = StringIndexOf;

class StringIncludes extends SymbolicValue {
    constructor(base, searchString, offset) {
        super();
        this.base = base;
        this.searchString = searchString;
    }

    visit(visitor) {
        visitor(this);
        this._visitChild(this.base, visitor);
        this._visitChild(this.searchString, visitor);
    }

    eval(model) {
        return String.prototype.includes.call(this.base.eval(model), this.searchString.eval(model));
    }

    toBooleanFormula() {
        return ["str.contains", this.base.toStringFormula(), this.searchString.toStringFormula()];
    }

    getType() {
        return Type.Boolean;
    }

    toFormula() {
        return ["Bool", this.toBooleanFormula()];
    }
}
exports.StringIncludes = StringIncludes;

class ArrayIncludes extends SymbolicValue {
    constructor(base, searchItem, offset) {
        super();
        this.base = base;
        this.searchItem = searchItem;
    }

    visit(visitor) {
        visitor(this);
        this._visitChild(this.base, visitor);
        this._visitChild(this.searchItem, visitor);
    }

    eval(model) {
        return String.prototype.includes.call(this.base.eval(model), this.searchItem.eval(model));
    }

    toBooleanFormula() {
       //TODO:
       return [];
    }

    getType() {
        return Type.Boolean;
    }

    toFormula() {
        return ["Bool", this.toBooleanFormula()];
    }
}
exports.ArrayIncludes = ArrayIncludes;

class StringToLowerCase extends SymbolicValue {
    constructor(base) {
        super();
        this.base = base;
    }

    visit(visitor) {
        visitor(this);
        this._visitChild(this.base, visitor);
    }

    eval(model) {
        return String.prototype.toLowerCase.call(this.base.eval(model));
    }

    getConstraints() {
        // FIXME: we require the input to be already lower-cased, so
        // js.toLowerCase can just be the identity function.
        return [["js.isLowerCase", this.base.toStringFormula()]];
    }

    toStringFormula() {
        return ["js.toLowerCase", this.base.toStringFormula()];
    }

    getType() {
        return Type.STRING;
    }

    toFormula() {
        return ["Str", this.toStringFormula()];
    }
}
exports.StringToLowerCase = StringToLowerCase;

class StringToUpperCase extends SymbolicValue {
    constructor(base) {
        super();
        this.base = base;
    }

    visit(visitor) {
        visitor(this);
        this._visitChild(this.base, visitor);
    }

    eval(model) {
        return String.prototype.toUpperCase.call(this.base.eval(model));
    }

    getConstraints() {
        // FIXME: we require the input to be already upper-cased, so
        // js.toUpperCase can just be the identity function.
        return [["js.isUpperCase", this.base.toStringFormula()]];
    }

    toStringFormula() {
        return ["js.toUpperCase", this.base.toStringFormula()];
    }

    getType() {
        return Type.STRING;
    }

    toFormula() {
        return ["Str", this.toStringFormula()];
    }
}
exports.StringToUpperCase = StringToUpperCase;

class StringCharCodeAt extends SymbolicValue {
    constructor(base, idx) {
        super();
        this.base = base;
        this.idx = idx;
    }

    visit(visitor) {
        visitor(this);
        this._visitChild(this.base, visitor);
        this._visitChild(this.idx, visitor);
    }

    eval(model) {
        return String.prototype.charCodeAt.call(
            this.base.eval(model), this.idx.eval(model)
        );
    }

    toIntegerFormula() {
        return ["js.charCodeAt", this.base.toStringFormula(), this.idx.toIntegerFormula()];
    }

    getType() {
        return Type.NUMBER;
    }

    toFormula() {
        return ["Num", this.toIntegerFormula()];
    }
}
exports.StringCharCodeAt = StringCharCodeAt;


class IsFinite extends SymbolicValue {
    constructor(val) {
        super();
        this.val = val;
    }

    visit(visitor) {
        visitor(this);
        this._visitChild(this.val, visitor);
    }

    eval(model) {
        return isFinite(this.val.eval(model));
    }

    toBooleanFormula() {
        return ["js.isFinite", this.val.toFormula()];
    }

    getType() {
        return Type.BOOLEAN;
    }

    toFormula() {
        return ["Boolean", this.toBooleanFormula()];
    }
}
exports.IsFinite = IsFinite;

class NumberIsFinite extends SymbolicValue {
    constructor(val) {
        super();
        this.val = val;
    }

    visit(visitor) {
        visitor(this);
        this._visitChild(this.val, visitor);
    }

    eval(model) {
        return Number.isFinite(this.val.eval(model));
    }

    toBooleanFormula() {
        return ["js.Number.isFinite", this.val.toFormula()];
    }

    getType() {
        return Type.BOOLEAN;
    }

    toFormula() {
        return ["Boolean", this.toBooleanFormula()];
    }
}
exports.NumberIsFinite = NumberIsFinite;

class IsNaN extends SymbolicValue {
    constructor(val) {
        super();
        this.val = val;
    }

    visit(visitor) {
        visitor(this);
        this._visitChild(this.val, visitor);
    }

    eval(model) {
        return isNaN(this.val.eval(model));
    }

    toBooleanFormula() {
        return ["js.isNaN", this.val.toFormula()];
    }

    getType() {
        return Type.BOOLEAN;
    }

    toFormula() {
        return ["Boolean", this.toBooleanFormula()];
    }
}
exports.IsNaN = IsNaN;

class NumberIsNaN extends SymbolicValue {
    constructor(val) {
        super();
        this.val = val;
    }

    visit(visitor) {
        visitor(this);
        this._visitChild(this.val, visitor);
    }

    eval(model) {
        return Number.isNaN(this.val.eval(model));
    }

    toBooleanFormula() {
        return ["js.Number.isNaN", this.val.toFormula()];
    }

    getType() {
        return Type.BOOLEAN;
    }

    toFormula() {
        return ["Boolean", this.toBooleanFormula()];
    }
}
exports.NumberIsNaN = NumberIsNaN;

class NumberToFixed extends SymbolicValue {
    constructor(base, fracDigits=new Constant(0)) {
        super();
        this.base = base;
        this.fracDigits = fracDigits;
    }

    visit(visitor) {
        visitor(this);
        this._visitChild(this.base, visitor);
        this._visitChild(this.fracDigits, visitor);
    }

    eval(model) {
        return Number.prototype.toFixed.call(this.base.eval(model), this.fracDigits.eval(model));
    }

    toStringFormula() {
        return ["js.toFixed", this.base.toIntegerFormula(), this.fracDigits.toIntegerFormula()];
    }

    getType() {
        return Type.STRING;
    }

    toFormula() {
        return ["Str", this.toStringFormula()];
    }
}
exports.NumberToFixed = NumberToFixed;

class MathAbs extends SymbolicValue {
    constructor(num) {
        super();
        this.num = num;
    }

    visit(visitor) {
        visitor(this);
        this._visitChild(this.num, visitor);
    }

    eval(model) {
        return Math.abs(this.num.eval(model));
    }

    toIntegerFormula() {
        return ["abs", this.num.toIntegerFormula()];
    }

    getType() {
        return Type.NUMBER;
    }

    toFormula() {
        return ["Num", this.toIntegerFormula()];
    }
}
exports.MathAbs = MathAbs;

class MathFloor extends SymbolicValue {
    constructor(num) {
        super();
        this.num = num;
    }

    visit(visitor) {
        visitor(this);
        this._visitChild(this.num, visitor);
    }

    eval(model) {
        return Math.floor(this.num.eval(model));
    }

    toIntegerFormula() {
        return ["floor", this.num.toIntegerFormula()];
    }

    getType() {
        return Type.NUMBER;
    }

    toFormula() {
        return ["Num", this.toIntegerFormula()];
    }
}
exports.MathFloor = MathFloor;

class MathCeil extends SymbolicValue {
    constructor(num) {
        super();
        this.num = num;
    }

    visit(visitor) {
        visitor(this);
        this._visitChild(this.num, visitor);
    }

    eval(model) {
        return Math.ceil(this.num.eval(model));
    }

    toIntegerFormula() {
        return ["ceil", this.num.toIntegerFormula()];
    }

    getType() {
        return Type.NUMBER;
    }

    toFormula() {
        return ["Num", this.toIntegerFormula()];
    }
}
exports.MathCeil = MathCeil;

class MathRound extends SymbolicValue {
    constructor(num) {
        super();
        this.num = num;
    }

    visit(visitor) {
        visitor(this);
        this._visitChild(this.num, visitor);
    }

    eval(model) {
        return Math.round(this.num.eval(model));
    }

    toIntegerFormula() {
        return ["round", this.num.toIntegerFormula()];
    }

    getType() {
        return Type.NUMBER;
    }

    toFormula() {
        return ["Num", this.toIntegerFormula()];
    }
}
exports.MathRound = MathRound;

class MathSqrt extends SymbolicValue {
    constructor(num) {
        super();
        this.num = num;
    }

    visit(visitor) {
        visitor(this);
        this._visitChild(this.num, visitor);
    }

    eval(model) {
        return Math.sqrt(this.num.eval(model));
    }

    toIntegerFormula() {
        return ["sqrt", this.num.toIntegerFormula()];
    }

    getType() {
        return Type.NUMBER;
    }

    toFormula() {
        return ["Num", this.toIntegerFormula()];
    }
}
exports.MathSqrt = MathSqrt;

const RegExpParser = require("./regexp");

class RegExpInstance extends SymbolicValue {
    constructor(regexp, instanceName) {
        super();
        this.regexp = regexp;
        this.instance = new Variable("regexp." + instanceName);
    }

    visit(visitor) {
        visitor(this);
        this._visitChild(this.regexp, visitor);
        this._visitChild(this.instance, visitor);
    }

    getConstraints() {
        if (!(this.regexp instanceof Constant)) {
            throw new Error("can't solve for non-constant regexes");
        }
        const val = this.regexp.value;
        const regexFormula = RegExpParser.parse(_.isRegExp(val) ? val.source : val);
        return [["str.in.re", this.instance.toStringFormula(), regexFormula.toRegexFormula()]];
    }

    toFormula() {
        return this.instance.toFormula();
    }
}

let namer = 0;
exports.resetNameCounter = function() {
    namer = 0;
};

function getTempName(name) {
    return name + "_" + namer++;
}

class StringSearch extends StringIndexOf {
    constructor(base, regexp) {
        super(base, new RegExpInstance(regexp, getTempName()));
    }

    eval(model) {
        return String.prototype.search.call(this.base.eval(model), this.searchString.regexp.eval(model));
    }
}
exports.StringSearch = StringSearch;

class RegExpTest extends SymbolicValue {
    constructor(base, str) {
        super();
        this.base = base;
        this.str = str;
    }

    visit(visitor) {
        visitor(this);
        this._visitChild(this.base, visitor);
        this._visitChild(this.str, visitor);
    }

    eval(model) {
        return RegExp.prototype.test.call(this.base.eval(model), this.str.eval(model));
    }

    toBooleanFormula() {
        if (!(this.base instanceof Constant)) {
            console.log(this.base);
            throw new Error("can't solve for non-constant regexes");
        }
        const val = this.base.value;
        const regexFormula = RegExpParser.parse(_.isRegExp(val) ? val.source : val);
        return ["str.in.re", this.str.toStringFormula(), regexFormula.toRegexFormula()];
    }

    toFormula() {
        return ["Boolean", this.toBooleanFormula()];
    }
}
exports.RegExpTest = RegExpTest;

class Temporary {
    constructor(name, sort) {
        this.name = name;
        this.sort = sort;
    }
}
exports.Temporary = Temporary;

const { CaptureVisitor } = require("./regexpast");

class RegExpExec extends SymbolicValue {
    constructor(regex, str) {
        super();
        this.regex = regex;
        this.str = str;

        this._temps = [];
        this._caps = [];
        this._resultObjId = getObjectId(this.regex.value);
        const genName = () => {
            const name = getTempName("regex_exec");
            this._temps.push(new Temporary(name, "String"));
            return name;
        };
        const genCapture = () => {
            const name = getTempName("regex_capture");
            const v = new Variable(name, Type.STRING | Type.UNDEFINED);
            this._caps.push(v);
            return name;
        };
        const visitor = new CaptureVisitor(genName, genCapture);
        this._formula = visitor.visit(this.getRegexAST(), genName());
    }

    visit(visitor) {
        visitor(this);
        this._visitChild(this.regex, visitor);
        this._visitChild(this.str, visitor);
        for (const v of this._temps) {
            this._visitChild(v, visitor);
        }
        for (const v of this._caps) {
            this._visitChild(v, visitor);
        }
    }

    eval(model) {
        return RegExp.prototype.exec.call(this.regex.eval(model), this.str.eval(model));
    }

    getRegexAST() {
        if (!(this.regex instanceof Constant)) {
            console.log(this.regex);
            throw new Error("can't solve for non-constant regexes");
        }
        const val = this.regex.value;
        const source = _.isRegExp(val) ? val.source : val;
        // console.log(source);
        const ast = RegExpParser.parse(source);
        // console.log(ast);
        return ast;
    }

    getConstraints() {
        return [
            ["=", ["GetProperties", String(this._resultObjId)], this.toObjectFormula()],
            this._formula
        ];
    }

    toBooleanFormula() {
        return ["=", ["Str", this._temps[0].name], this.str.toFormula()];//, ["str.in.re", this._temps[0].name, this.getRegexAST().toRegexFormula()]];
    }

    toObjectFormula() {
        let result = ["store", "EmptyObject", '"0"', ["Just", ["Str", this._temps[0].name]]];
        for (let i = 0; i < this._caps.length; ++i) {
            result = ["store", result, '"' + (i + 1) + '"', ["Just", this._caps[i].name]];
        }
        return result;
    }

    toFormula() {
        return ["ite", this.toBooleanFormula(), ["Obj", String(this._resultObjId)], "null"];
    }
}
exports.RegExpExec = RegExpExec;

class StringReplace extends SymbolicValue {
    constructor(base, searchString, replacement) {
        super();
        this.base = base;
        this.searchString = searchString;
        this.replacement = replacement;
    }

    visit(visitor) {
        visitor(this);
        this._visitChild(this.base, visitor);
        this._visitChild(this.searchString, visitor);
        this._visitChild(this.replacement, visitor);
    }

    eval(model) {
        return String.prototype.replace.call(this.base.eval(model), this.searchString.eval(model), this.replacement.eval(model));
    }

    toStringFormula() {
        return ["str.replace", this.base.toStringFormula(), this.searchString.toStringFormula(), this.replacement.toStringFormula()];
    }

    getType() {
        return Type.STRING;
    }

    toFormula() {
        return ["Str", this.toStringFormula()];
    }
}
exports.StringReplace = StringReplace;

class ProgramObjectValue extends SymbolicValue {
    constructor(id, value) {
        super();
        this.id = id;
        this.value = value;
    }

    visit(visitor) {
        visitor(this);
        this._visitChild(this.value, visitor);
    }

    toObjectFormula() {
        return ["GetProperties", String(this.id)];
    }

    getType() {
        return Type.OBJECT;
    }

    toFormula() {
        return ["Obj", String(this.id)];
    }
}

class ObjectValueConstructor extends ProgramObjectValue {
    constructor(concResult, symbolicArg) {
        super(getObjectId(concResult), symbolicArg);
    }
}

class ToObject extends ObjectValueConstructor {
    eval(model) {
        return Object(this.value.eval(model));
    }

    toObjectFormula() {
        return ["js.ToObject", this.value.toFormula()];
    }
}
exports.ToObject = ToObject;

class NewObject extends ObjectValueConstructor {
    eval(model) {
        return new Object(this.value.eval(model));
    }

    toObjectFormula() {
        return ["js.NewObject", this.value.toFormula()];
    }
}
exports.NewObject = NewObject;

class NewArray extends ObjectValueConstructor {
    eval(model) {
        return new Array(this.value.eval(model));
    }

    toObjectFormula() {
        return ["js.constructArray", this.value.toFormula()];
    }
}
exports.NewArray = NewArray;

function Cast(type) {
    return class extends SymbolicValue {
        constructor(value) {
            super();
            this.value = value;
        }

        visit(visitor) {
            visitor(this);
            this._visitChild(this.value, visitor);
        }

        getType() {
            return type;
        }
    };
}

class ToString extends Cast(Type.STRING) {
    eval(model) {
        return String(this.value.eval(model));
    }

    toStringFormula() {
        return this.value.toStringFormula();
    }

    toFormula() {
        return ["Str", this.toStringFormula()];
    }

    toObjectFormula() {
        return ["StringToObject", this.value.toStringFormula()];
    }
}
exports.ToString = ToString;

class NewString extends ObjectValueConstructor {
    eval(model) {
        return new String(this.value.eval(model));
    }

    toStringFormula() {
        return this.value.toStringFormula();
    }

    toObjectFormula() {
        return ["StringToObject", this.value.toStringFormula()];
    }
}
exports.NewString = NewString;

class ToNumber extends Cast(Type.NUMBER) {
    eval(model) {
        return Number(this.value.eval(model));
    }

    toIntegerFormula() {
        return this.value.toIntegerFormula();
    }

    toObjectFormula() {
        return ["NumberToObject", this.value.toIntegerFormula()];
    }

    toFormula() {
        return ["Num", this.toIntegerFormula()];
    }
}
exports.ToNumber = ToNumber;

class NewNumber extends ObjectValueConstructor {
    eval(model) {
        return new Number(this.value.eval(model));
    }

    toIntegerFormula() {
        return this.value.toIntegerFormula();
    }

    toObjectFormula() {
        return ["NumberToObject", this.value.toIntegerFormula()];
    }
}
exports.NewNumber = NewNumber;

class ToBoolean extends Cast(Type.BOOLEAN) {
    eval(model) {
        return Boolean(this.value.eval(model));
    }

    toBooleanFormula() {
        return this.value.toBooleanFormula();
    }

    toObjectFormula() {
        return ["BooleanToObject", this.value.toBooleanFormula()];
    }

    toFormula() {
        return ["Boolean", this.toIntegerFormula()];
    }
}
exports.ToBoolean = ToBoolean;

class NewBoolean extends ObjectValueConstructor {
    eval(model) {
        return new Boolean(this.value.eval(model));
    }

    toBooleanFormula() {
        return this.value.toBooleanFormula();
    }

    toObjectFormula() {
        return ["BooleanToObject", this.value.toBooleanFormula()];
    }
}
exports.NewBoolean = NewBoolean;

class NewRegExp extends SymbolicValue {
    constructor(concRegExp, pattern, flags) {
        super();
        this.id = getObjectId(concRegExp);
        this.pattern = pattern;
        this.flags = flags;
    }

    eval(model) {
        return new RegExp(this.pattern.eval(model), this.flags.eval(model));
    }

    toObjectFormula() {
        return ["js.constructRegExp", this.pattern.toStringFormula(), this.flags.toStringFormula()];
    }

    toFormula() {
        return ["Obj", String(this.id)];
    }
}
exports.NewRegExp = NewRegExp;

class ParseInt extends SymbolicValue {
    constructor(str, radix) {
        super();
        this.str = str;
        this.radix = radix;

        this._ws = new Temporary(getTempName("parseInt.ws"), "String");
        this._numPart = new Temporary(getTempName("parseInt.numPart"), "String");
        this._rem = new Temporary(getTempName("parseInt.rem"), "String");
        this._i = new Temporary(getTempName("parseInt.i"), "Int");
    }

    visit(visitor) {
        visitor(this);
        visitor(this.str);
        visitor(this.radix);
        visitor(this._ws);
        visitor(this._numPart);
        visitor(this._rem);
        visitor(this._i);
    }

    eval(model) {
        return parseInt(this.str.eval(model), this.radix.eval(model));
    }

    getConstraints() {
        return [["ParseIntCondition", this.str.toStringFormula(), this.radix.toIntegerFormula(), this._ws.name, this._numPart.name, this._rem.name, this._i.name]];
    }

    toIntegerFormula() {
        return this._i.name;
    }

    toFormula() {
        return ["Num", this._i.name];
    }
}
exports.ParseInt = ParseInt;
