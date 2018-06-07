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
        this.solution = {}                        
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
        return this.process_output(String(res.stdout).split('\n'))
    }
    
    addConstraints(stack) {
       for (var i in stack)
         console.log(stack[i]);
    }
    
    process_output(data) {
        for (var i in data) {
            const line = data[i]
            const j = line.indexOf(' = ')
            if (j !== -1) {
                // XYZ_varN = val;
                const id = "var" + line[j - 1];
                const pref = line.slice(0, 3);
                const val = line.slice(j + 3, line.length - 1);
                if (!this.solution[id])
                    this.solution[id] = {"TYP": null, "REP": null, "LOC": null};
                this.solution[id][pref] = val                
            } 
            else if (line.includes('---------'))
                return "sat";
            else if (line.includes('=====UNSATISFIABLE====='))
                return "unsat";
            else
                return "unknown"
        }        
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
        return this.solution
    }
    
    close() {
        //FIXME: Just for compatibility. To be removed?
    }

};
