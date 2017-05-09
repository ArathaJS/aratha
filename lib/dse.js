"use strict";

const _ = require("lodash");

const Constraint = require("./constraint");
const {SymbolicValue, Constant, PutField, Variable} = require("./symbolic");
const Type = require("./type");

const TYPE_MAP = {
    "undefined": Type.UNDEFINED,
    "null": Type.NULL,
    "number": Type.NUMBER,
    "string": Type.STRING,
    "boolean": Type.BOOLEAN,
    "object": Type.OBJECT
};

class TypeConstraint {
    constructor(type, subject, value) {
        this.type = type;
        if (subject instanceof PutField) {
            // We can only talk about types symbolic values of type Val, so we
            // need to get the base value, before any of our modifications.
            subject = subject.getTopBase();
        }

        this.subject = subject;
        this.value = value === undefined ? true : value;
    }

    isTrueIn(model) {
        let val = this.subject;
        if (val instanceof SymbolicValue) {
            val = val.eval(model);
        }
        return this.type.has(TYPE_MAP[typeof val]) === this.value;
    }

    negate() {
        this.value = !this.value;
    }

    toFormula() {
        if (this.subject instanceof Constant) {
            // We have a concrete subject. Therefore, this type constraint is
            // independent of any symbolic variables.
            if (this.type.has(TYPE_MAP[typeof this.subject.value]) === this.value) {
                return "true";
            } else {
                return "false";
            }
        } else {
            console.log(this.subject);
            const formula = this.type.constraintFor(this.subject.toFormula());
            return this.value ? formula : ["not", formula];
        }
    }

    getId() { return this.type.types.toString() + (this.subject.name || String(this.subject)); }
}


class ExecutionPath {
    constructor(constraints) {
        this.constraints = constraints || [];
    }

    isEmpty() { return this.constraints.length === 0; }

    addConstraint(expr, concreteValue) {
        const constraint = new Constraint(expr, concreteValue);
        if (!_.some(this.constraints, constraint)) {
            this.constraints.push(constraint);
        }
    }

    addTypeConstraint(type, subject, value) {
        const constraint = new TypeConstraint(type, subject, value);
        if (!_.some(this.constraints, constraint)) {
            this.constraints.push(constraint);
        }
    }

    clear() { this.constraints.length = 0; }

    getPrefix(length) {
        return new ExecutionPath(this.constraints.slice(0, length));
    }
}

exports.ExecutionPath = ExecutionPath;

class Trie {
    constructor() {
        this._root = {};
    }

    add(s) {
        let node = this._root;
        for (let i = 0; i < s.length; i++) {
            const w = s[i];
            if (!node.hasOwnProperty(w))
                node[w] = {};
            node = node[w];
        }
    }

    hasPrefix(s) {
        let node = this._root;
        for (let i = 0; i < s.length; i++) {
            const w = s[i];
            if (!node.hasOwnProperty(w))
                return false;
            node = node[w];
        }
        return true;
    }
}

class ExecutionPathSet {
    constructor() {
        this._paths = new Trie();
    }

    add(path) { this._paths.add(this._encode(path)); return this; }

    hasPrefix(path) { return this._paths.hasPrefix(this._encode(path)); }

    _encode(path) {
        return _.map(path.constraints,
            (c) => (c.value ? "" : "!") + c.getId());
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

function collectObjectConstants(expr) {
    const objects = {};

    if (expr instanceof SymbolicValue) {
        expr.visit((expr) => {
            if (expr instanceof Constant && _.isObject(expr.value)) {
                objects[expr.objectId] = expr.toObjectFormula();
            }
        });
    } else {
        _.forEach(expr, (v) => Object.assign(objects, collectObjectConstants(v)));
    }

    return objects;
}

function parseNumericExpr(expr) {
    if (typeof expr === "string")
        return parseFloat(expr, 10);

    const args = _.map(expr.slice(1), parseNumericExpr);
    switch (expr[0]) {
        case "-":
            return _.reduce(args, (total, x) => total - x, 0);
        case "/":
            return args[0] / args[1];
        default:
            throw new Error("unknown operator " + expr[0]);
    }
}

function parsePrimitive(value) {
    if (value === "undefined") { return undefined; }
    if (value === "null") { return null; }

    const type = value[0],
        contents = value[1];
    switch (type) {
        case "Boolean":
            return contents === "true";
        case "Num":
            return parseNumericExpr(contents);
        case "Str":
            return contents.replace(/\\x([a-fA-F0-9]{2})/g, (a, b) => {
                return String.fromCharCode(parseInt(b, 16));
            });
        default:
            throw new Error("invalid primitive " + value.toString());
    }
}

function isVarName(name) {
    return name.startsWith("var");
}

function parseITEEqualsChain(chain, varName, output) {
    while (chain[0] === "ite") {
        const if_ = chain[1];
        const op = if_[0],
            lhs = if_[1],
            rhs = if_[2];

        if (op !== "=")
            throw new Error(`expected =, got ${op}`);

        let key;
        if (lhs === varName) {
            key = rhs;
        } else if (rhs === varName) {
            key = lhs;
        } else {
            throw new Error(`missing variable name ${varName} in ${if_}`);
        }
        // Output the then clause.
        output[key] = chain[2];

        // Continue down the else clause.
        chain = chain[3];
    }

    // Return the last else clause.
    return chain;
}

function parseMapFunction(fun, output) {
    return parseITEEqualsChain(fun.expr, fun.args[0][0], output);
}

function parseModel(model) {
    const objects = {};

    function parseModelValue(value) {
        if (value[0] === "Obj") {
            const objId = value[1];
            if (!objects.hasOwnProperty(objId)) {
                objects[objId] = {};
            }
            return objects[objId];
        } else {
            return parsePrimitive(value);
        }
    }

    const solution = {};
    const funs = {};
    for (let i = 1; i < model.length; i++) {
        const sentence = model[i];
        if (sentence[0] === "define-fun") {
            const name = sentence[1];
            const value = sentence[4];
            funs[name] = { args: sentence[2], expr: value };
            if (!isVarName(name))
                continue;
            solution[name] = parseModelValue(value);
        } else if (sentence[0] === "declare-datatypes") {
            continue;
        } else {
            console.warn("unknown model sentence", sentence);
        }
    }

    function extractObjectModel(expr) {
        if (expr[0] === "_" && expr[1] === "as-array") {
            const model = {};
            const modelName = expr[2];
            parseMapFunction(funs[modelName], model);
            return model;
        } else if (expr[0] === "store") {
            const base = extractObjectModel(expr[1]);
            base[expr[2]] = expr[3];
            return base;
        } else if (expr[0][0] === "as", expr[0][1] === "const") {
            return {};
        } else {
            console.error(expr);
            throw new Error("invalid object expression " + expr);
        }
    }

    function parseObjectModel(expr) {
        for (const k in expr) {
            if (expr.hasOwnProperty(k)) {
                if (expr[k] === "Nothing") {
                    delete expr[k];
                } else {
                    expr[k] = parseModelValue(expr[k][1]);
                }
            }
        }
        return expr;
    }

    const getProperties = funs.GetProperties;
    if (getProperties) {
        const objModelExprs = {};
        const fallbackExpr = parseMapFunction(getProperties, objModelExprs);

        _.forEach(objModelExprs, (expr, id) => {
            const objModel = parseObjectModel(extractObjectModel(expr));
            if (!objects.hasOwnProperty(id))
                objects[id] = {};
            Object.assign(objects[id], objModel);
            delete objects[id];
        });

        const fallbackModel = parseObjectModel(extractObjectModel(fallbackExpr));
        _.forEach(objects, (obj) => {
            Object.assign(obj, fallbackModel);
        });
    }

    return solution;
}

function declareVar(solver, v) {
    solver.declareConst(v.name, "Val");
}

function defineObjectConstant(solver, id, value) {
    solver.assert(["=", ["GetProperties", id], value]);
}

class DSE {
    constructor(solver, program) {
        this._solver = solver;
        this._program = program;
        this._inputs = [{}];
        this._visitedPaths = new ExecutionPathSet();
    }

    execute() {
        const input = this._nextInput();
        console.log("testing input: ", input);
        const path = this._program(input);
        console.log("executed path: ", this._visitedPaths._encode(path));
        return this._processPath(path);
    }

    isDone() {
        return this._inputs.length === 0;
    }

    _processPath(path) {
        this._visitedPaths.add(path);
        return this._generateInputs(path);
    }

    _nextInput() { return this._inputs.shift(); }

    async _generateInputs(path) {
        const solver = this._solver;

        for (let i = 0; i < path.constraints.length; i++) {
            path.constraints[i].negate();
            const prefix = path.getPrefix(i + 1);
            if (!this._visitedPaths.hasPrefix(prefix)) {
                this._visitedPaths.add(prefix);
                console.log("solving prefix", this._visitedPaths._encode(prefix));
                solver.push(1);

                const variables = collectVariables(prefix.constraints);
                const objects = collectObjectConstants(prefix.constraints);
                _.forEach(variables, (v) => declareVar(solver, v));
                _.forEach(objects, (v, k) => defineObjectConstant(solver, k, v));
                _.forEach(prefix.constraints, (c) => solver.assert(c.toFormula()));

                const status = await solver.checkSat();
                console.log(status);
                if (status === "sat") {
                    const model = await solver.getModel();
                    const parsed = parseModel(model);
                    console.log(parsed);
                    _.forEach(prefix.constraints, (c2) => {
                        if (!c2.isTrueIn(parsed)) {
                            throw new Error(`model failed to validate constraint: ${c2}`);
                        }
                    });
                    this._inputs.push(parsed);
                }

                solver.pop(1);
            }
            path.constraints[i].negate();
        }
    }

    async _generateInputsIncremental(path) {
        const variables = {};
        const solver = this._solver;

        solver.push(1);
        for (let i = 0; i < path.constraints.length; i++) {
            const c = path.constraints[i];

            const freeVars = collectVariables(c);
            _.forEach(freeVars, (v, k) => {
                if (!variables.hasOwnProperty(k)) {
                    variables[k] = v;
                    declareVar(solver, v);
                }
            });

            c.negate();
            if (!this._visitedPaths.hasPrefix(path.getPrefix(i + 1))) {
                solver.push(1);

                solver.assert(c.toFormula());
                const status = await solver.checkSat();
                if (status === "sat") {
                    const model = await solver.getModel();
                    this._inputs.push(parseModel(model));
                }

                solver.pop(1);
            }
            c.negate();

            if (i < path.constraints.length - 1) {
                solver.assert(c.toFormula());
            }
        }
        solver.pop(1);
    }
}

exports.DSE = DSE;
