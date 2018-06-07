"use strict";

const fs = require("fs");

const _ = require("lodash");

const sexpr = require("./sexpr");

const { TypeConstraint } = require("./constraint");

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
           this.addConstraint(stack[i]);
    }
    
    addConstraint(cons) {
        if (cons instanceof TypeConstraint)
            this.mzn_buffer += "constraint TYP_" + cons.subject.name + " in " 
                            + cons.type.toJSType() + ";\n";
        else
            console.log("boolean constraint: ", String(cons))
    }
    
    process_output(data) {
        for (var i in data) {
            const line = data[i]
            const j = line.indexOf(' = ')
            if (j !== -1) {
                // XYZ_varN = val;
                const id = "var" + line[j - 1];
                const val = line.slice(j + 3, line.length - 1);
                const pref = line.slice(0, 3);                
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

    getSolution() {
//        console.log(this.solution)
        return this.solution
    }
    
    close() {
        //FIXME: Just for compatibility. To be removed?
    }

};


function parseSolution(solution) {
    var model = {}
    for (var v in solution) {
        var sol;
        switch (Number(solution[v].TYP)) {
           case 1:
               sol = undefined;
               break;
           case 2:
               sol = null;
               break;
           case 3:
               sol = solution[v].REP === "true";
               break;
           case 4:
               sol = Number(solution[v].REP);
               break;
           case 5:
               sol = solution[v].REP;
               break;
           case 6:
               sol = solution[v].REP; //FIXME: Object TBD!!!
               break;                                                                    
        }
        model[v] = sol;
    }
    return model;
}

exports.parseSolution = parseSolution;

