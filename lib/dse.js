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
        console.log(path);
        return _.map(path, (c) => (c.value ? "" : "!") + c.getId());
    }
}

class ConstraintCollector {
    constructor(solver) {
        this.solver = solver;

        this.constraints = [];
        this.variables = {};
        this.objectConstants = {};
        this.extraConstraints = [];

        this._solverStack = 0;
    }

    push(constraint) {
        this.constraints.push(constraint);
        this._collectVariables(constraint);
        this._collectObjectConstants(constraint);
        this._collectExtraConstraints(constraint);
    }

    _collect(expr, f) {
        if (expr instanceof SymbolicValue) {
            expr.visit(f);
        } else {
            _.forEach(expr, (v) => this._collect(v, f));
        }
    }

    _collectVariables(expr) {
        this._collect(expr, (expr) => {
            if (expr instanceof Variable) {
                this.variables[expr.name] = expr;
            }
        });
    }

    _collectObjectConstants(expr) {
        this._collect(expr, (expr) => {
            if (expr instanceof Constant && _.isObject(expr.value)) {
                this.objectConstants[expr.objectId] = expr.toObjectFormula();
            }
        });
    }

    _collectExtraConstraints(expr) {
        this._collect(expr, (expr) => {
            _.forEach(expr.getConstraints(), (c) => this.extraConstraints.push(c));
        });
    }


    pushNegated(constraint) {
        constraint.negate();
        this.push(constraint);
    }

    negateTop() {
        _.last(this.constraints).negate();
    }

    checkSat() {
        this._popSolver();
        this._pushSolver();
        this._declareVars();
        this._defineObjectConstants();
        this._assertExtraConstraints();
        this._assertConstraints();
        return this.solver.checkSat();
    }

    _declareVars() {
        _.forEach(this.variables, (v) => this.solver.declareConst(v.name, "Val"));
    }

    _defineObjectConstants() {
        _.forEach(this.objectConstants, (o, id) => this.solver.assert(["=", ["GetProperties", id], o]));
    }

    _assertExtraConstraints() {
        _.forEach(this.extraConstraints, (c) => this.solver.assert(c));
    }

    _assertConstraints() {
        _.forEach(this.constraints, (c) => this.solver.assert(c.toFormula()));
    }

    async getModel() {
        const model = parseModel(await this.solver.getModel());
        this.verifyModel(model);
        return model;
    }

    verifyModel(model) {
        _.forEach(this.constraints, (c) => {
            if (!c.isTrueIn(model)) {
                console.log(model);
                throw new Error(`model failed to validate constraint: ${c}`);
            }
        });
    }

    clear() {
        this._popSolver();
    }

    _pushSolver() {
        this.solver.push(1);
        this._solverStack += 1;
    }

    _popSolver() {
        if (this._solverStack > 0) {
            this.solver.pop(1);
        }
    }
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
        console.log("executed path: ", this._visitedPaths._encode(path.constraints));
        return this._processPath(path);
    }

    isDone() {
        return this._inputs.length === 0;
    }

    _processPath(path) {
        this._visitedPaths.add(path.constraints);
        return this._generateInputs(path);
    }

    _nextInput() { return this._inputs.shift(); }
    _addInput(input) { this._inputs.push(input); }

    async _generateInputs(path) {
        const solver = this._solver;
        const collector = new ConstraintCollector(solver);
        const constraints = path.constraints;

        for (let i = 0; i < constraints.length; i++) {
            collector.pushNegated(constraints[i]);
            if (!this._visitedPaths.hasPrefix(collector.constraints)) {
                const status = await collector.checkSat();
                if (status === "sat") {
                    this._addInput(await collector.getModel());
                }
            }
            collector.negateTop();
        }
        collector.clear();
    }
}

exports.DSE = DSE;
