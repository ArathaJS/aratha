"use strict";

const fs = require("fs");

const _ = require("lodash");

const sexpr = require("./sexpr");

exports.SMTSolver = class SMTSolver {

    constructor(process) {
        this._callbackQueue = [];
        this._commandLogs = [];

        process.stdout.setEncoding("utf8");
        process.stderr.setEncoding("utf8");

        const parser = new sexpr.Parser();
        process.stdout.on("data", (data) => {
            const comments = data.trim().split("\n").map((s) => "; " + s).join("\n") + "\n";
            for (let i = 0; i < this._commandLogs.length; i++) {
                this._commandLogs[i].write(comments, "utf8");
            }
            parser.parse(data, (stmt) => {
                this._consume(stmt);
            });
        });

        process.stderr.on("data", console.error);
        process.stdin.on("error", console.error);

        this.process = process;
    }
    
    isCPSolver() { return false; }

    logCommands(stream) {
        this._commandLogs.push(stream);
    }

    loadFiles(paths) {
        _.forEach(paths, (path) => {
            this._write(fs.readFileSync(path, { encoding: "utf8" }));
        });
    }

    push(n) {
        this._send(["push", n.toString()]);
    }

    pop(n) {
        this._send(["pop", n.toString()]);
    }

    async checkSat() {
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
        try {
            this._send(["exit"]);
        } catch (e) {
            console.error("error while closing:", e);
        }
    }

    _send(command) {
        this._write(sexpr.stringify(command) + "\n");
    }

    _write(output) {
        for (let i = 0; i < this._commandLogs.length; i++) {
            this._commandLogs[i].write(output, "utf8");
        }
        this.process.stdin.write(output);
    }

    async _enqueueCallback(callback) {
        this._callbackQueue.push(callback);
    }

    _consume(stmt) {
        const callback = this._callbackQueue.shift();
        if (callback) {
            callback(stmt);
        } else {
            console.error(`received ${stmt}, but there is no callback`);
        }
    }

    async _getResponse() {
        return new Promise((resolve, reject) => {
            this._enqueueCallback((stmt) => {
                if (stmt[0] !== "error") {
                    resolve(stmt);
                } else {
                   // FIXME: Workaround to avoid Error: write EPIPE
                   // at WriteWrap.afterWrite [as oncomplete]
                   console.log(stmt[1]);
                   fail
                   //reject(new Error(stmt[1]));
                }
            });
        });
    }
};
