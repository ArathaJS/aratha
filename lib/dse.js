"use strict";

const _ = require("lodash");
// const Immutable = require("immutable");

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
        // if (!_.some(this.constraints, constraint)) {
            this.constraints.push(constraint);
            // console.log("adding constraint", constraint.getId());
        // }
    }

    addTypeConstraint(type, subject, value) {
        const constraint = new TypeConstraint(type, subject, value);
        if (!_.some(this.constraints, constraint)) {
            this.constraints.push(constraint);
        }
    }
}

exports.ExecutionPath = ExecutionPath;

class Trie {
    constructor() {
        this._root = {};
    }

    add(s) {
        let isNew = false;
        let node = this._root;
        for (let i = 0; i < s.length; i++) {
            const w = s[i];
            if (!node.hasOwnProperty(w)) {
                node[w] = {};
                isNew = true;
            }
            node = node[w];
        }
        return isNew;
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

    add(path) { return this._paths.add(this._encode(path)); }

    hasPrefix(path) { return this._paths.hasPrefix(this._encode(path)); }

    _encode(path) {
        // return _.map(path, (c) => (c.value ? "" : "!") + c.getId());
        return _.map(path, (c) => c.value);
    }
}
exports.ExecutionPathSet = ExecutionPathSet;

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
    if (subset.size > superset.size) {
        return false;
    }
    for (var elem of subset) {
        if (!superset.has(elem)) {
            return false;
        }
    }
    return true;
}

class UnsatCoreSet {
    constructor(maxSize=Infinity) {
        this._cores = [];
        this.maxSize = maxSize;
    }

    add(core) {
        core = normalizeCore(core);
        if (!this._has(core)) {
            this._cores.push(core);
            if (this._cores.length > this.maxSize) {
                this._cores.shift();
            }
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
    constructor(solver, incremental=false) {
        this.solver = solver;
        this.incremental = incremental;
        this._solverStack = [this._createLevel()];
        this._assertionCount = 0;
    }

    _createLevel() {
        return {
            constraints: [],
            extraConstraints: [],
            variables: new Set(),
            objectConstants: new Map(),
            assertionsByName: new Map()
        }
    }

    _top() { return _.last(this._solverStack); }

    push(constraint) {
        if (this.incremental || this._solverStack.length <= 1) {
            this._pushSolver();
        }
        const top = this._top();
        this._collectVariables(constraint);
        this._collectObjectConstants(constraint);
        this._collectExtraConstraints(constraint);
        top.constraints.push(constraint);
        this._assert(constraint.toFormula());
    }

    _collect(expr, f) {
        const stack = [expr];
        while (stack.length > 0) {
            const e = stack.shift();
            if (e instanceof SymbolicValue) {
                e.visit(f);
            } else if (_.isArray(e)) {
                stack.push(...e);
            } else if (_.isObject(e)) {
                _.forOwn(e, (v) => stack.push(v));
            }
        }
    }

    _isVarDeclared(name) {
        for (const level of this._solverStack) {
            if (level.variables.has(name)) {
                return true;
            }
        }
        return false;
    }

    _collectVariables(expr) {
        const top = this._top();
        this._collect(expr, (expr) => {
            if (expr instanceof Variable) {
                if (!this._isVarDeclared(expr.name)) {
                    top.variables.add(expr.name);
                    this.solver.declareConst(expr.name, "Val");
                }
            }
        });
    }

    _collectObjectConstants(expr) {
        const top = this._top();
        this._collect(expr, (expr) => {
            if (expr instanceof Constant && _.isObject(expr.value)) {
                const id = expr.objectId;
                const formula = expr.toObjectFormula();
                top.objectConstants.set(expr.objectId, expr.toObjectFormula());
                this._assert(["=", ["GetProperties", String(id)], formula]);
            }
        });
    }

    _collectExtraConstraints(expr) {
        const top = this._top();
        this._collect(expr, (expr) => {
            _.forEach(expr.getConstraints(), (c) => {
                top.extraConstraints.push(c);
                this._assert(c.toFormula());
            });
        });
    }


    pushNegated(constraint) {
        constraint.negate();
        this.push(constraint);
    }

    negateTop() {
        const top = this._top()
        _.last(top.constraints).negate();
        this.solver.pop(1);
        this.solver.push(1);
        for (const v of top.variables) {
            this.solver.declareConst(v, "Val");
        }
        for (const a of this._getLevelAssertions(top)) {
            this._assert(a);
        }
    }

    _getLevelAssertions(level=this._top()) {
        const assertions = [];
        for (const [id, formula] of level.objectConstants) {
            assertions.push(["=", ["GetProperties", String(id)], formula]);
        }
        _.forEach(level.extraConstraints, (c) => assertions.push(c));
        _.forEach(level.constraints, (c) => assertions.push(c.toFormula()));
        return assertions;
    }

    getAssertions() {
        return _.flatten(_.map(this._solverStack, (l) => this._getLevelAssertions(l)));
    }

    getConstraints() {
        return _.flatten(_.map(this._solverStack, (l) => l.constraints));
    }

    checkSat() {
        return this.solver.checkSat();
    }

    async getModel() {
        const model = parseModel(await this.solver.getModel());
        this.verifyModel(model);
        return model;
    }

    verifyModel(model) {
        for (const level of this._solverStack) {
            for (const c of level.constraints) {
                if (!c.isTrueIn(model)) {
                    console.error(`model error: constraint (= ${c.value} ${c}) failed to validate in ${JSON.stringify(model)}`);
                    return false;
                }
            }
        }
        return true;
    }

    clear() {
        if (this._solverStack.length > 1) {
            this.solver.pop(this._solverStack.length - 1);
            this._solverStack.length = 1;
        }
    }

    _pushSolver() {
        this.solver.push(1);
        this._solverStack.push(this._createLevel());
    }

    // _popSolver() {
    //     if (this._solverStack.length > 1) {
    //         this.solver.pop(1);
    //         this._solverStack.pop();
    //     }
    // }

    _assert(formula) {
        const topLevel = _.last(this._solverStack);
        const name = "p" + this._assertionCount++;
        topLevel.assertionsByName.set(name, sexpr.stringify(formula));
        formula = ["!", formula, ":named", name];
        return this.solver.assert(formula);
    }

    getNamedFormula(name) {
        for (const level of this._solverStack) {
            const assertion = level.assertionsByName.get(name);
            if (assertion !== undefined) {
                return assertion;
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
    constructor(solver, program, options) {
        _.defaults(options, {
            incremental: true,
            unsatCores: false,
            coreCacheSize: 8
        });
        this._solver = solver;
        this._collector = new ConstraintCollector(solver, options.incremental);
        this._program = program;
        this._inputs = [{}];
        this._visitedPaths = new ExecutionPathSet();
        this._unsatCores = new UnsatCoreSet(options.coreCacheSize);
        this._candidateCores = new UnsatCoreSet();
        this._workQueue = [];
        this.useUnsatCores = options.unsatCores;
    }

    async execute() {
        const input = await this._nextInput();
        if (input === undefined) {
            return;
        }

        console.log("testing input: ", input);
        const path = this._program(input);
        console.log("execution complete");

        const constraints = path.constraints;
        console.log(constraints.length + " constraints in path condition");
        // for(var i = 0; i < constraints.length; i++) {
        //     var c = constraints[i];
        //     var id = c.getId();
        //     var len = id.length;
        //     console.log("len(" + i + ") =", len);
        // }
        // console.log("executed path: ", this._visitedPaths._encode(constraints));

        if (this._visitedPaths.add(constraints)) {
            console.log("adding new constraint set to work queue");
            Object.defineProperty(constraints, "length", { configurable: false, writable: false });
            this._workQueue.push({step: 0, constraints: constraints});
        }
    }

    isDone() {
        return this._inputs.length === 0 && this._workQueue.length === 0;
    }

    async _nextInput() {
        if (this._inputs.length === 0) {
            await this._generateInput();
        }
        return this._inputs.shift();
    }

    _addInput(input) { this._inputs.push(input); }

    _inUnsatCore(assertions) {
        if (!this.useUnsatCores) {
            return false;
        }
        console.log("checking unsat cores");
        return this._unsatCores.match(assertions);
    }

    async _generateInput() {
        while(this._workQueue.length > 0 && await this._tryGenerateNextInput() !== "sat");
    }

    async _tryGenerateNextInput() {
        if (this._workQueue.length === 0) {
            throw new Error("can't generate inputs: work queue empty");
        }

        const workItem = this._workQueue[0];
        const constraints = workItem.constraints;
        const collector = this._collector;
        let status = "unknown";
        const i = workItem.step;
        // console.log("step", i, constraints);
        workItem.step++;

        const prefix = constraints.slice(0, i + 1);
        prefix[i].negate();
        if (!this._visitedPaths.hasPrefix(prefix)) {
            this._visitedPaths.add(prefix);
            if (i > 0) {
                const preCheckStatus = await collector.checkSat();
                if (preCheckStatus !== "sat") {
                    this._workQueue.shift();
                    console.log(`abandoning work item: pre-check failed at step ${i}: ${preCheckStatus}`);
                    // console.log("constraints =", collector.getConstraints());
                    collector.clear();
                    return preCheckStatus;
                }
            }

            collector.push(prefix[i]);
            const assertions = collector.getAssertions();
            if (!this._inUnsatCore(assertions)) {
                console.log(`solving ![${i}]`);
                // console.log("constraints =", collector.getConstraints());
                status = await collector.checkSat();
                console.log(status);
                if (status === "sat") {
                    this._addInput(await collector.getModel());
                } else if (status === "unsat" && this.useUnsatCores) {
                    const core = await collector.getUnsatCore();
                    if (this._candidateCores.has(core)) {
                        console.log("adding unsat core:", core);
                        if(!this._unsatCores.add(core)) {
                            console.log("unsat core already present: ", core);
                        }
                    } else {
                        this._candidateCores.add(core);
                    }
                }
            } else {
                status = "unsat";
                console.log("unsat core pruned");
            }
            collector.negateTop();
            console.log("negated top");
        } else {
            prefix[i].negate();
            collector.push(prefix[i]);
            status = "visited";
            console.log("prefix pruned");
        }

        if (workItem.step >= constraints.length) {
            this._workQueue.shift();
            collector.clear();
            console.log("finished work item");
        }
        return status;
    }
}

exports.DSE = DSE;
