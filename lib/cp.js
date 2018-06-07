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
        this.mzn_buffer = [
            "include \"javascript.mzn\"", "int: NUM_OBJS", "int: NUM_WRITES",
            "int: NUM_BUILTIN"
        ]
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
        this.write(
            this.mzn, this.mzn_buffer.join(";\n") + ";\nsolve satisfy;\n"
        );
//        console.log(this.mzn_buffer);
        const res = child_process.spawnSync(this.cmd, [this.mzn, this.dzn]);
        if (res.status != 0) {
            console.log(String(res.stderr))
            return undefined
        }
        this.mzn_buffer.push("% =====SOLVED=====");
        return this.process_output(String(res.stdout).split('\n'))
    }
    
    addConstraint(cons) {
        if (cons instanceof TypeConstraint) {
            console.log("type constraint: " + cons)
            this.mzn_buffer.push("constraint TYP_" + cons.subject.name + 
                " in " + cons.type.toJSType());
        }
        else {
            console.log("constraint: " + cons)
            this.mzn_buffer.push("% constraint " + cons);
        }    
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
            this.mzn_buffer.push("var " + type.toJSType() + t);
        else
            this.mzn_buffer.push("var JS_TYPE: " + t);
        this.mzn_buffer.push("var string: "  + r);
        this.mzn_buffer.push("var 0..NUM_OBJS: " + l);
        this.mzn_buffer.push(
            "constraint js_var(" + t + ", " + r + ", " + l + ")"
        );
        console.log("Declared " + name)
    }
    
    pop(n) {
      var m = this.mzn_buffer.length - 2;
      while (n > 0) {
          m = this.mzn_buffer.lastIndexOf("% =====SOLVED=====", m);
          n--;
      }
      this.mzn_buffer = this.mzn_buffer.slice(0, m);
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

