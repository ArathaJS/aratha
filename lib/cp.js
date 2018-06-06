"use strict";

const fs = require("fs");

const _ = require("lodash");

const sexpr = require("./sexpr");

exports.CPSolver = class CPSolver {
    constructor(process) {
        this._callbackQueue = [];
        this._commandLogs = [];

        process.stdout.setEncoding("utf8");
        process.stderr.setEncoding("utf8");

        const parser = new sexpr.Parser();
        process.stdout.on("data", (data) => {
            const comments = data.trim().split("\n").map((s) => "% " + s).join("\n") + "\n";
            for (let i = 0; i < this._commandLogs.length; i++) {
                this._commandLogs[i].write(comments, "utf8");
            }
            parser.parse(data, (stmt) => {
                this._consume(stmt);
            });
        });

        process.stderr.on("data", console.error);

        this.process = process;
    }
    
    isCPSolver() { return true; }

    logCommands(stream) {
        this._commandLogs.push(stream);
    }

    loadFiles(paths) {
        _.forEach(paths, (path) => {
            this._write(fs.readFileSync(path, { encoding: "utf8" }));
        });
    }

    solveSat() {
        this._send(["solve satisfy"]);
        return this._getResponse();
    }
    
    declareVar(name, type) {
        var decl;
        if (type) {
            const loc = type.valueConforms("object") ? "" : " = 0";
            decl = "var " + type.toJSType() + " TYP_" + name + ";\n" +
                   "var string: REP_" + name + ";\n" +
                   "var int: LOC_"    + name + loc;
            
        }
        else
            decl = "var JS_TYPE TYP_" + name + ";\n" +
                   "var string: REP_" + name + ";\n" +
                   "var int: LOC_"    + name;
        this._send([decl]);
    }

    getModel() { //FIXME:
        console.log("TODO: get-model")
    }

    close() {
        try {
            this._send(["exit"]);
        } catch (e) {
            console.error("error while closing:", e);
        }
    }

    _send(command) {
//        process.stdout.write(sexpr.stringify(command, 1) + ";\n");
        this._write(sexpr.stringify(command, 1) + ";\n");
    }

    _write(output) {
        for (let i = 0; i < this._commandLogs.length; i++) {
            this._commandLogs[i].write(output, "utf8");
        }
        this.process.stdin.write(output);
    }

    _enqueueCallback(callback) {
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

    _getResponse() {
        return new Promise((resolve, reject) => {
            this._enqueueCallback((stmt) => {
                if (stmt[0] !== "error") {
                    resolve(stmt);
                } else {
                    reject(new Error(stmt[1]));
                }
            });
        });
    }
};
