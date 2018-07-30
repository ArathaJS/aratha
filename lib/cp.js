"use strict";

const fs = require("fs");

const Type = require("./type");

const _ = require("lodash");

const sexpr = require("./sexpr");

const { toMZNConstraint } = require("./mzn-constraint");

const child_process = require("child_process");

const JSTypes = [
    "Null", "Undef", "Bool", "Num", "Str", "Array", "Function", "Object"
]

exports.CPSolver = class CPSolver {

    constructor() {
        this.preamble = 
            "include \"javascript.mzn\";\ninclude \"alldifferent_except_0.mzn" +
            "\";\ninclude \"increasing.mzn\";\nint: MIN_LOC;\nint: N_LOCS;" +
            "\nint: N_IMPL_PROPS;\nint: N_EXPL_PROPS;\n";
        this.mznHead = "";
        this.mznBody = [ "" ];
        this.solution = {};
        this.N_LOCS = 0;
        this.MIN_LOC = 1;
        this.N_IMPL_PROPS = 0;
        this.N_EXPL_PROPS = 0;        
    }
    
    isCPSolver() { return true; }

    write(file, text) {
        fs.writeFileSync(file, text, function (err) { if (err) throw err; });
    }
    
    checkRes(res, t, d) {
        if (res.status != 0) {       
            if (res.status === 124)
                console.log("Timeout (" + t + " seconds) expired!");
            else {
                console.log(String(res.stderr));
                if (d)
                    throw new Error("Solving error!");
            }          
            return false
        }
        return true;
    }
    
    runSolver(opt) {
        if (opt.twoSteps) {
            var res = child_process.spawnSync("timeout", 
                [opt.mzn2fznTimeout, this.mzn2fzn()].concat(opt.mzn2fznArgs)
                    .concat([opt.mznPath, opt.dznPath])
            );
            if (!this.checkRes(res, opt.mzn2fznTimeout))
                return undefined;
            res = child_process.spawnSync("timeout", 
                [opt.fznTimeout, this.fzn()].concat(opt.fznArgs).concat(
                    [opt.fznPath])
            );
            if (!this.checkRes(res, opt.fznTimeout))
                return undefined;
        }
        else {
            const res = child_process.spawnSync("timeout", 
                [opt.mznTimeout, this.mzn].concat(opt.mznArgs).concat(
                    [opt.mznPath, opt.dznPath])
            );
            if (!this.checkRes(res, opt.mznTimeout))
                return undefined;
        
        }
        if (opt.debug)
            console.log(String(res.stdout));
        return res;
    }
        
    getSearch(h, vars) {
        switch (h) {
            case "typs":
                var t = ""
                for (let v of vars)
                    t += "TYP_" + v + ", ";
                return "::int_search([" + t + "], first_fail, indomain_min, " +
                    "complete)";
            default:
                return "";                
        }
    }

    solveSat(vars, opt) {
//        console.log(vars)
        const mzn_model = (
            this.preamble + this.mznHead + this.declareVars(vars) +
            Array.from(new Set(this.mznBody)).join('') + "solve " + 
            this.getSearch(opt.solve, vars) + " satisfy;\n"
        );
        const dzn_data = "N_LOCS = " + this.N_LOCS + ";\nN_EXPL_PROPS = " + 
            this.N_EXPL_PROPS + ";\nN_IMPL_PROPS = " + this.N_IMPL_PROPS + 
            ";\nMIN_LOC = " + this.MIN_LOC + ";"
        this.write(opt.mznPath, mzn_model); 
        this.write(opt.dznPath, dzn_data);
        if (opt.debug) {
          const c = child_process.spawnSync("cat",[opt.mznPath, opt.dznPath])
          console.log(String(c.stdout))
        }
        const res = this.runSolver(opt);
        if (!res)
            return undefined;
        this.mznHead = "";        
        this.N_LOCS = 0;
        this.MIN_LOC = 1;
        this.N_IMPL_PROPS = 0;
        this.N_EXPL_PROPS = 0;
        return this.process_output(String(res.stdout).split('\n'))
    }
    
    addConstraint(cons) {
        this.mznBody.push(toMZNConstraint(cons, this) + ";\n");
    }
    
    process_output(data) {
//        console.log(data)
        for (var i in data) {
            const line = data[i];
            const j = line.indexOf(' = ');
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
                const pref = line.slice(0, 3);
                const id = "var" + line[j - 1];
                const val = line.slice(j + 3, line.length - 1);
                // line[j + 3] === "[" ? line.slice(j + 4, line.indexOf("..")) :
                if (!this.solution[id])
                    this.solution[id] = {"TYP": null, "REP": null, "LOC": null};
//                console.log(id, pref, val);
                this.solution[id][pref] = val;
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
        return decls + "constraint alldifferent_except_0([" + vlist + "]);\n" + 
                       "constraint increasing([" + vlist + "]);\n"
    };
    
    declareVar(name, type) {
        var decl = "";
        const t = "TYP_" + name
        const r = "REP_" + name
        const l = "LOC_" + name
        if (type) {
            decl += "var " + type.toJSType() + t;
            if (type.has(Type.OBJECT))
                this.N_LOCS++;
        }
        else {
            decl += "var JSType: " + t;
            this.N_LOCS++;
        }
        decl += ";\nvar string: "  + r + ";\nvar {0} union MIN_LOC..N_LOCS: " +l+ 
                ";\nconstraint js_var(" + t + ", " + r + ", " + l + ");\n";
//        console.log("Declared " + name)
        return decl
    }
    
    pop(n) {
//        console.log("Pop " + n, this.mznBody);
        this.mznBody = this.mznBody.slice(0, this.mznBody.length - n);
    }

    getSolution() {
//        console.log(this.solution)
        return this.solution
    }
    
    close() {
        //FIXME: Just for compatibility. To be removed?
    }

};

function toObj(typ, loc, solution) {
    var obj;
    switch (typ) {
        case 6:
           obj = new Array
        case 7:
           obj = new Function
        case 8:
           obj = new Object    
    }
    for (var i = 0; i < solution["LOCS"].length; ++i)
        if (solution["LOCS"][i] === loc) { 
            const typ = solution["TYPS"][i]; 
            const ref = solution["REFS"][i];
            if (typ <= 5)
                obj[solution["KEYS"][i]] = toVal(typ, ref, solution["REPS"][i])
            else
                obj[solution["KEYS"][i]] = toObj(typ, ref, solution);
        }
    return obj;
}

function toVal(typ, loc, rep) {
    switch (JSTypes[Number(typ) - 1]) {
        case "Undef":
            return undefined;
        case "Null":
            return null;
        case "Bool":
            return loc === 0 ? rep === "true" : new Boolean(rep === "true");
        case "Num":
            return loc === 0 ? Number(rep) : new Number(rep);
        case "Str":
            return loc === 0 ? rep : new String(rep);
        default:
            throw new Error("Undefined type", typ);
    }
}

function parseSolution(solution) {
    var model = {}
    for (var v in solution)
        if (v.startsWith("var")) {
            const typ = Number(solution[v].TYP);
            const loc = Number(solution[v].LOC);
            if (typ <= 5)
                model[v] = toVal(typ, loc, solution[v].REP);
            else
                model[v] = toObj(typ, loc, solution);
//            console.log(v, model[v]);
        }
    return model;
}

exports.parseSolution = parseSolution;

