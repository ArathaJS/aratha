"use strict";

const _ = require("lodash");

const {BooleanConstraint, TypeConstraint} = require("./constraint");
const {SymbolicValue, Constant, Variable} = require("./symbolic");
const {parseModel} = require("./model");
const sexpr = require("./sexpr");

class ExecutionPath {
    constructor(constraints) {
        this.constraints = constraints || [];
    }

    isEmpty() { return this.constraints.length === 0; }

    addConstraint(expr, concreteValue) {
        const constraint = new BooleanConstraint(expr, concreteValue);
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

function normalizeVarNames(p, names) {
    if (_.isArray(p)) {
        return p.map((x) => normalizeVarNames(x, names));
    } else if (_.isString(p)) {
        const result = p.match(/var\d+/);
        if (result !== null) {
            if (names.has(p)) {
                return names.get(p);
            } else {
                const newName = "revar" + names.size;
                names.set(p, newName);
                return newName;
            }
        }
    } else {
        throw new Error("unknown term: " + p);
    }
    return p;
}

function parseAssertions(assertions) {
    const parser = new sexpr.Parser();
    const parsed = [];
    assertions.forEach((s) => {
        parser.parse(s, (p) => parsed.push(p));
    });
    return parsed;
}

function matchCoreStmts(core, query, names) {
    // console.log("matching deeper");
    if (core.size === 0) {
        // console.log("successfully matched", query);
        return true;
    }
    const attempted = new Set();
    for (let queryStmt of query) {
        const newNames = new Map(names);
        const normalizedQuery = sexpr.stringify(normalizeVarNames(queryStmt, newNames));
        if (attempted.has(normalizedQuery)) {
            continue;
        }
        // console.log("attempting to match", normalizedQuery, "against", core);
        // console.log("newNames=", newNames);
        if (core.delete(normalizedQuery)) {
            // console.log("successfully removed " + normalizedQuery);
            const didMatch = matchCoreStmts(core, query, newNames);
            core.add(normalizedQuery);
            if (didMatch) {
                return true;
            }
            // console.log("retrying match");
        }
        attempted.add(normalizedQuery);
    }
    // console.log("matching failed on", query);
    return false;
}

function coreMatches(core, query) {
    if (core.size > query.length) {
        console.log("core bigger than query: ", core.size, " > ", query.length);
        return false;
    }
    return matchCoreStmts(new Set(core), parseAssertions(query.map(sexpr.stringify)), new Map());
}

function normalizeCore(assertions) {
    const names = new Map();
    return new Set(parseAssertions(assertions).map(_.flow([(x) => normalizeVarNames(x, names), sexpr.stringify])));
}

function isSuperset(superset, subset) {
    for (var elem of subset) {
        if (!superset.has(elem)) {
            return false;
        }
    }
    return true;
}

class UnsatCoreSet {
    constructor() {
        this._cores = [];
    }

    add(core) {
        core = normalizeCore(core);
        if (!this._has(core)) {
            this._cores.push(core);
            return core;
        }
    }

    has(core) {
        return this._has(normalizeCore(core));
    }

    _has(core) {
        for (const x of this._cores) {
            if (isSuperset(core, x)) {
                return true;
            }
        }
        return false;
    }

    match(assertions) {
        for (let i = 0; i < this._cores.length; i++) {
            const core = this._cores[i];
            if (coreMatches(core, assertions)) {
                console.log("core", core, "matches", assertions);
                return true;
            }
        }
        return false;
    }
}

class ConstraintCollector {
    constructor(solver) {
        this.solver = solver;

        this.constraints = [];
        this.variables = {};
        this.objectConstants = {};
        this.extraConstraints = [];

        this._solverStack = [new Map()];
        this._assertionCount = 0;
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

    getAssertions() {
        const assertions = [];
        _.forEach(this.objectConstants, (o, id) => assertions.push(["=", ["GetProperties", id], o]));
        _.forEach(this.extraConstraints, (c) => assertions.push(c));
        _.forEach(this.constraints, (c) => assertions.push(c.toFormula()));
        return assertions;
    }

    checkSat() {
        this._popSolver();
        this._pushSolver();
        this._declareVars();
        _.forEach(this.getAssertions(), (a) => this._assert(a));

        return this.solver.checkSat();
    }

    _declareVars() {
        _.forEach(this.variables, (v) => this.solver.declareConst(v.name, "Val"));
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
        this._solverStack.push(new Map());
    }

    _popSolver() {
        if (this._solverStack.length > 1) {
            this.solver.pop(1);
            this._solverStack.pop();
        }
    }

    _assert(formula) {
        const name = "p" + this._assertionCount++;
        _.last(this._solverStack).set(name, sexpr.stringify(formula));
        formula = ["!", formula, ":named", name];
        return this.solver.assert(formula);
    }

    getNamedFormula(name) {
        for (let i = 0; i < this._solverStack.length; i++) {
            const props = this._solverStack[i];
            if (props.has(name)) {
                return props.get(name);
            }
        }
        throw new Error("unknown formula name " + name);
    }

    async getUnsatCore() {
        const coreNames = await this.solver.getUnsatCore();
        const core = new Set();
        for (let i = 0; i < coreNames.length; ++i) {
            core.add(this.getNamedFormula(coreNames[i]));
        }
        return core;
    }
}

class DSE {
    constructor(solver, program) {
        this._solver = solver;
        this._program = program;
        this._inputs = [{}];
        this._visitedPaths = new ExecutionPathSet();
        this._unsatCores = new UnsatCoreSet();
        this._candidateCores = new UnsatCoreSet();
        this.useUnsatCores = true;
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
        const candidateCores = this._candidateCores;

        for (let i = 0; i < constraints.length; i++) {
            collector.pushNegated(constraints[i]);
            if (!this._visitedPaths.hasPrefix(collector.constraints)) {
                const assertions = collector.getAssertions();
                console.log("testing for unsat core...");
                if (!this.useUnsatCores || !this._unsatCores.match(assertions)) {
                    // console.log("could not match unsat: ", sexpr.stringify(assertions));
                    const status = await collector.checkSat();
                    if (status === "sat") {
                        this._addInput(await collector.getModel());
                    } else if (status === "unsat" && this.useUnsatCores) {
                        const core = await collector.getUnsatCore();
                        if (candidateCores.has(core)) {
                            console.log("adding unsat core:", core);
                            if(!this._unsatCores.add(core)) {
                                console.log("unsat core already present: ", core);
                            }
                        } else {
                            candidateCores.add(core);
                        }
                    }
                } else {
                    console.log("unsat core pruned");
                }
            } else {
                console.log("prefix pruned");
            }
            collector.negateTop();
        }
        collector.clear();
    }
}

exports.DSE = DSE;
