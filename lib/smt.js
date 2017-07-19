"use strict";

const fs = require("fs");

const _ = require("lodash");

const sexpr = require("./sexpr");

exports.Solver = class Solver {
    constructor(process) {
        this._callbackQueue = [];

        process.stdout.setEncoding("utf8");
        process.stderr.setEncoding("utf8");

        const parser = new sexpr.Parser();
        process.stdout.on("data", (data) => {
            parser.parse(data, (stmt) => {
                this._consume(stmt);
            });
        });

        process.stderr.on("data", console.error);

        this.process = process;
    }

    loadFiles(paths) {
        _.forEach(paths, (path) => {
            this.process.stdin.write(fs.readFileSync(path));
        });
    }

    push(n) {
        this._send(["push", n.toString()]);
    }

    pop(n) {
        this._send(["pop", n.toString()]);
    }

    checkSat() {
        this._send(["check-sat"]);
        return this._getResponse();
    }

    declareConst(name, sort) {
        this._send(["declare-const", name, sort]);
    }

    assert(formula) {
        this._send(["assert", formula]);
    }

    getValue(vars) {
        this._send(["get-value", vars]);
        return this._getResponse();
    }

    getModel() {
        this._send(["get-model"]);
        return this._getResponse();
    }

    getUnsatCore() {
        this._send(["get-unsat-core"]);
        return this._getResponse();
    }

    close() {
        this.process.stdin.end("(exit)");
    }

    _send(command) {
        const cmdString = sexpr.stringify(command);
        console.log(cmdString);
        this.process.stdin.write(cmdString + "\n");
    }

    _enqueueCallback(callback) {
        this._callbackQueue.push(callback);
    }

    _consume(stmt) {
        const callback = this._callbackQueue.shift();
        if (callback) {
            callback(stmt);
        } else {
            throw new Error(`received ${stmt}, but there is no callback`);
        }
    }

    _getResponse() {
        return new Promise((resolve) => {
            this._enqueueCallback((stmt) => {
                if (stmt[0] !== "error") {
                    resolve(stmt);
                } else {
                    throw new Error(stmt[1]);
                }
            });
        });
    }
};
