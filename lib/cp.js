"use strict";

const fs = require("fs");

const _ = require("lodash");

const sexpr = require("./sexpr");

const child_process = require("child_process");

exports.CPSolver = class CPSolver {

    constructor(cmd, model, data) {
        this.cmd = cmd;
        this.mzn = model;
        this.dzn = data;
        this.mzn_buffer = "include \"javascript.mzn\";\nint: NUM_OBJS;\n" 
                        + "int: NUM_WRITES;\nint: NUM_BUILTIN;\n";
    }
    
    isCPSolver() { return true; }

    write(file, text) {
        fs. writeFileSync(file, text, function (err) { if (err) throw err; });
    }

    solveSat() {
        // FIXME: Temporary workaround for dzn.
        this.write(
            this.dzn, "NUM_OBJS = 5;\nNUM_WRITES = 5;\nNUM_BUILTIN = 5;\n"
        );
        this.write(this.mzn, this.mzn_buffer + "solve satisfy;\n");
        const res = child_process.spawnSync(this.cmd, [this.mzn, this.dzn]);
        if (res.status != 0) {
            console.log(String(res.stderr))
            return undefined
        }
        console.log(this.process_output(String(res.stdout)))
        return this.process_output(String(res.stdout))
    }
    
    process_output(data) {
        console.log(data) //FIXME: for line in data.
        if (data.includes('---------'))
            return "sat";
        else if (data.includes('=====UNSATISFIABLE====='))
            return "unsat";
        else
            return "unknown";
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
        this.mzn_buffer += 
            decl + t + ";\nvar string: "  + r + ";\nvar 0..NUM_OBJS: " + l + 
            ";\n" +  "constraint js_var(" + t + ", " + r + ", " + l + ");\n";
    }

    getModel() {
        console.log("TODO: get-model")
    }
    
    close() {
        //FIXME: Just for compatibility. To be removed?
    }

};
