"use strict";

// FIXME: Turn into external parameters.
const DEBUG = 1;
const TIMEOUT = String(3);

const fs = require("fs");

const _ = require("lodash");

const sexpr = require("./sexpr");

const { TypeConstraint } = require("./constraint");

const { toMZNConstraint } = require("./mzn-constraint");

const child_process = require("child_process");

const JSTypes = [
    "Null", "Undef", "Bool", "Num", "Str", "Boolean", "Number", "String", 
    "Array", "Function", "Object"
]

exports.CPSolver = class CPSolver {

    constructor(cmd, model, data) {
        this.cmd = cmd;
        this.mzn_file = model;
        this.dzn_file = data;
        this.preamble = 
            "include \"javascript.mzn\";\ninclude \"alldifferent_except_0.mzn\";\n" + 
            "int: NLOCS;\nint: NWRITES;\nint: NBUILTINS;\n"
        this.mzn_model = [ "% Model\n" ];
        this.solution = {};
        this.NLOCS = 0;
        this.NWRITES = 0;
        this.NBUILTINS = 0;
    }
    
    isCPSolver() { return true; }

    write(file, text) {
        fs.writeFileSync(file, text, function (err) { if (err) throw err; });
    }

    solveSat(vars) {        
//        console.log(vars)
        this.write(
            this.mzn_file, this.preamble + this.declareVars(vars) +
            this.mzn_model[this.mzn_model.length - 1] + "solve satisfy;\n"
        );
        this.write(
            this.dzn_file, "NLOCS = " + this.NLOCS + ";\nNWRITES = " 
            + this.NWRITES + ";\nNBUILTINS = " + this.NBUILTINS + ";\n"
        );
        if (DEBUG) {
          const c = child_process.spawnSync("cat", [this.mzn_file, this.dzn_file]);
          console.log(String(c.stdout))
        }
        const res = child_process.spawnSync(
            "timeout", [TIMEOUT, this.cmd, this.mzn_file, this.dzn_file]
        );
        this.builtins = ""
        this.NLOCS = 0;
        this.NWRITES = 0;
        this.NBUILTINS = 0;
        if (res.status != 0) {            
            if (res.status === 124)
                console.log("Timeout (" + TIMEOUT + " seconds) expired!");
            else {
                console.log(String(res.stderr));
                if (DEBUG)
                    throw new Error("Solving error!");
            }          
            return undefined
        }
        if (DEBUG) {
            console.log(String(res.stdout))
        }
        return this.process_output(String(res.stdout).split('\n'))
    }
    
    addConstraint(cons) {
        if (cons instanceof TypeConstraint) {
            if (cons.subject.name)
                this.mzn_model[this.mzn_model.length - 1] += "constraint TYP_" + 
                cons.subject.name + " in " + cons.type.toJSType() + ";\n";
            //FIXME: else?
        }
        else 
            this.mzn_model[this.mzn_model.length - 1] += 
            toMZNConstraint(cons, this) + ";\n";
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
    
    declareVars(vars) {
        var decls = "";
        var vlist =  "";
        for (let v of vars) {
            vlist += "LOC_" + v + ", ";
            decls += this.declareVar(v);
        }
        return "constraint alldifferent_except_0([" + vlist + "]);\n" + decls;
    };
    
    declareVar(name, type) {
        var decl = "";
        const t = "TYP_" + name
        const r = "REP_" + name
        const l = "LOC_" + name
        if (type) {
            decl += "var " + type.toJSType() + t;
            if (type.has(Type.OBJECT))
                this.NLOCS++;
        }
        else {
            decl += "var JSType: " + t;
            this.NLOCS++;
        }
        decl += ";\nvar string: "  + r + ";\nvar 0..NLOCS: " + l + 
                ";\nconstraint js_var(" + t + ", " + r + ", " + l + ");\n";
//        console.log("Declared " + name)
        return decl
    }
    
    pop(n) {
      this.mzn_model = this.mzn_model.slice(0, this.mzn_model.length - n);
      this.mzn_model.push("% Model\n");
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
//        console.log(v, solution[v])
        switch (JSTypes[Number(solution[v].TYP) - 1]) {
           case "Undef":
               sol = undefined;
               break;
           case "Null":
               sol = null;
               break;
           case "Bool":
           case "Boolean":
               sol = (solution[v].REP === "true");
               break;
           case "Num":
           case "Number":
               sol = Number(solution[v].REP);
               break;
           case "Str":
           case "String":
           default: //FIXME: Add other types!
               sol = solution[v].REP;
               break;                                                                    
        }
        model[v] = sol;
    }
    return model;
}

exports.parseSolution = parseSolution;

