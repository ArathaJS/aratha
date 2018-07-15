"use strict";

// FIXME: Turn into external parameters.
const DEBUG = 1;
const TIMEOUT = String(2);

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
            "include \"javascript.mzn\";\ninclude \"alldifferent_except_0.mzn" +
            "\";\nint: MINLOC;\nint: NLOCS;\nint: NWRITES;\nint: NBUILTINS;\n"
        this.mzn_header = "";
        this.mzn_body = [ "% Model\n" ];
        this.solution = {};
        this.NLOCS = 0;
        this.MINLOC = 1;
        this.NWRITES = 0;
        this.NBUILTINS = 0;
    }
    
    isCPSolver() { return true; }

    write(file, text) {
        fs.writeFileSync(file, text, function (err) { if (err) throw err; });
    }

    solveSat(vars) {        
//        console.log(vars)
        const mzn_model = (
            this.preamble + this.mzn_header + this.declareVars(vars) +
            this.mzn_body[this.mzn_body.length - 1] + "solve satisfy;\n"
        );
        this.write(this.mzn_file, mzn_model); 
        this.write(
            this.dzn_file, "NLOCS = " + this.NLOCS + ";\nNWRITES = " +
            + this.NWRITES + ";\nNBUILTINS = " + this.NBUILTINS + ";\nMINLOC = "
            + this.MINLOC + ";"
        );
        if (DEBUG) {
          const c = child_process.spawnSync("cat", [this.mzn_file, this.dzn_file]);
          console.log(String(c.stdout))
        }
        const res = child_process.spawnSync(
            "timeout", [TIMEOUT, this.cmd, this.mzn_file, this.dzn_file]
        );
        this.mzn_header = "";
        this.NLOCS = 0;
        this.MINLOC = 1;
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
                this.mzn_body[this.mzn_body.length - 1] += "constraint TYP_" + 
                cons.subject.name + " in " + cons.type.toJSType() + ";\n";
            //FIXME: else?
        }
        else 
            this.mzn_body[this.mzn_body.length - 1] += 
            toMZNConstraint(cons, this) + ";\n";
    }
    
    process_output(data) {
        for (var i in data) {
            const line = data[i]
            const j = line.indexOf(' = ')
            if (j !== -1) {
                // array
                if (line[j - 1] === "S") {
                    const id = line.slice(0, j);
                    const val = id === "LOCS" || id === "REFS" ? 
                        eval(line.slice(line.indexOf('['), line.length - 2)) :
                        // FIXME: Workaround, FlatZinc output needs to be fixed!
                        eval(('["' + line.slice(
                            line.indexOf('[') + 1, line.length - 3) + '"]')
                            .replace(/, /g, '" , "'));
                    if (val.length > 1)
                        this.solution[id] = val.slice(1, val.length);   
                    continue;
                }
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
        decl += ";\nvar string: "  + r + ";\nvar {0} union MINLOC..NLOCS: " +l+ 
                ";\nconstraint js_var(" + t + ", " + r + ", " + l + ");\n";
//        console.log("Declared " + name)
        return decl
    }
    
    pop(n) {
      this.mzn_body = this.mzn_body.slice(0, this.mzn_body.length - n);
      this.mzn_body.push("% Model\n");
    }

    getSolution() {
//        console.log(this.solution)
        return this.solution
    }
    
    close() {
        //FIXME: Just for compatibility. To be removed?
    }

};

function toObj(loc, solution) {
    var obj = {}; 
    for (var i = 0; i < solution["LOCS"]; ++i)
        if (solution["LOCS"][i] === loc) { 
            const ref = solution["REFS"][i]; 
            if (ref === 0)
                obj[solution["KEYS"][i]] = toVal(
                    solution["TYPS"][i], solution["REPS"][i]
                )
            else
                obj[solution["KEYS"][i]] = toObj(ref, solution);
        }
    return obj;
}

function toVal(typ, rep) {
    switch (JSTypes[Number(typ) - 1]) {
        case "Undef":
            return undefined;
        case "Null":
            return null;
        case "Bool":
        case "Boolean":
            return rep === "true";
        case "Num":
        case "Number":
            return Number(rep);
        case "Str":
        case "String":
            return rep;
        default:
            throw new Error("Undefined type", typ);
    }
}

function parseSolution(solution) {
    var model = {}
    for (var v in solution)
        if (v.startsWith("var")) {
            const loc = Number(solution[v].LOC);
            if (loc === 0)
                model[v] = toVal(solution[v].TYP, solution[v].REP);
            else
                model[v] = toObj(loc, solution);
//            console.log(v, model[v]);
        }
    return model;
}

exports.parseSolution = parseSolution;

