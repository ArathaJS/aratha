"use strict";

const _ = require("lodash");

const {EqualityConstraint, TypeConstraint} = require("./constraint");
const {SymbolicValue, Constant, Variable} = require("./symbolic");
const {parseModel} = require("./model");

class ExecutionPath {
    constructor(constraints) {
        this.constraints = constraints || [];
    }

    isEmpty() { return this.constraints.length === 0; }

    addConstraint(expr, concreteValue) {
        const constraint = new EqualityConstraint(expr, concreteValue);
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

function collectExtraConstraints(expr) {
    const constraints = [];

    if (expr instanceof SymbolicValue) {
        expr.visit((expr) => {
            _.forEach(expr.getConstraints(), (c) => constraints.push(c));
        });
    } else {
        _.forEach(expr, (v) => Object.assign(constraints, collectExtraConstraints(v)));
    }

    return constraints;
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
                const extraConstraints = collectExtraConstraints(prefix.constraints);
                _.forEach(variables, (v) => declareVar(solver, v));
                _.forEach(objects, (v, k) => defineObjectConstant(solver, k, v));
                _.forEach(extraConstraints, (c) => solver.assert(c));
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
