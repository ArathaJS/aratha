"use strict";

const fs = require("fs");

const _ = require("lodash");

const sexpr = require("./sexpr");

const { TypeConstraint } = require("./constraint");

const { toMZNConstraint } = require("./mzn-constraint");

const child_process = require("child_process");

const JSTypes = ["Null", "Undef", "Bool", "Num", "Str", "Boolean", "Number", "String", "Array", "Function", "Object"]

exports.CPSolver = class CPSolver {

    constructor(cmd, model, data) {
        this.cmd = cmd;
        this.mzn = model;
        this.dzn = data;
        this.mzn_buffer = [
            "include \"javascript.mzn\"", "include \"alldifferent_except_0.mzn\"",
            "int: NLOCS", "int: NWRITES", "int: NBUILTINS"
        ];
        this.builtins = ""
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
            this.mzn, this.declareVars(vars) + this.builtins
                    + _.uniq(this.mzn_buffer).join(";\n") + ";\nsolve satisfy;\n"
        );
        this.write(
            this.dzn, "NLOCS = " + this.NLOCS
                 + ";\nNWRITES = " + this.NWRITES
                 + ";\nNBUILTINS = " + this.NBUILTINS + ";\n"
        );
        console.log("% Model")
        const c = child_process.spawnSync("cat", [this.mzn, this.dzn]);
        console.log(String(c.stdout))
        const res = child_process.spawnSync(this.cmd, [this.mzn, this.dzn]);
        if (res.status != 0) {
            console.log(String(res.stderr))
            return undefined
        }
        this.mzn_buffer.push("% =====POP=====");
        this.builtins = ""
        this.NLOCS = 0;
        this.NWRITES = 0;
        this.NBUILTINS = 0;
        return this.process_output(String(res.stdout).split('\n'))
    }
    
    addConstraint(cons) {
        if (cons instanceof TypeConstraint)
            this.mzn_buffer.push("constraint TYP_" + cons.subject.name + 
                " in " + cons.type.toJSType());
        else 
            this.mzn_buffer.push(toMZNConstraint(cons, this));
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
            this.NLOCS++;
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
                this.NUM_LOCS++;
        }
        else {
            decl += "var JSType: " + t;
            this.NUM_LOCS++;
        }
        decl += ";\nvar string: "  + r + ";\nvar 0..NLOCS: " + l + 
                ";\nconstraint js_var(" + t + ", " + r + ", " + l + ");\n";
//        console.log("Declared " + name)
        return decl
    }
    
    pop(n) {
      var m = this.mzn_buffer.length - 2;
      while (n > 0) {
          m = this.mzn_buffer.lastIndexOf("% =====POP=====", m);
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

