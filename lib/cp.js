"use strict";

const fs = require("fs");

const _ = require("lodash");

const sexpr = require("./sexpr");

const child_process = require("child_process");

exports.CPSolver = class CPSolver {

    constructor(cmd, model, data, preamble) {
        this.cmd = cmd;
        this.mzn = model;
        this.dzn = data;
        this.mzn_stream = fs.createWriteStream(this.mzn);
        this.dzn_stream = fs.createWriteStream(this.dzn);
        this.mzn_stream.write("include \"javascript.mzn\";\n");
        this.mzn_stream.write("int: NUM_OBJS;\n");
        this.mzn_stream.write("int: NUM_WRITES;\n");
        this.mzn_stream.write("int: NUM_BUILTIN;\n");
    }
    
    solve() {
        return child_process.spawnSync(this.cmd, [this.mzn, this.dzn]);
    }
    
    isCPSolver() { return true; }

    solveSat() {
        // FIXME: Temporary workaround for dzn.
        this.dzn_stream.write("NUM_OBJS    = 5;\n");
        this.dzn_stream.write("NUM_WRITES  = 5;\n");
        this.dzn_stream.write("NUM_BUILTIN = 5;\n");
        this.mzn_stream.write("solve satisfy;\n");
        console.log(this.solve())
    }
    
    declareVar(name, type) {
        var decl;
        const t = "TYP_" + name
        const r = "REP_" + name
        const l = "LOC_" + name
        if (type)
            decl = "var " + type.toJSType();
        else
            decl = "var JS_TYPE: ";
        decl += t + ";\nvar string: "  + r + ";\nvar 0..NUM_OBJS: " + l + ";\n";
        this.mzn_stream.write(decl);
        this.mzn_stream.write(
            "constraint js_var(" + t + ", " + r + ", " + l+ ");\n"
        );
    }

    getModel() {
        console.log("TODO: get-model")
    }
    
    close() {
        try {
            this.mzn_stream.close();
            this.dzn_stream.close();
        } 
        catch (e) {
            console.error("Error while closing:", e);
        }
    }

};
