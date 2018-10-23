"use strict";

const fs = require("fs");

const Type = require("./type");

const _ = require("lodash");

const sexpr = require("./sexpr");

const { addMiniZincConstraint } = require("./mzn-constraint");

const child_process = require("child_process");

const JSTypes = [
    "Null", "Undef", "Bool", "Num", "Str", "Array", "Function", "Object"
]

var CP_PID = null;
function get_cp_pid() { return CP_PID };

exports.CPSolver = class CPSolver {

    constructor(options) {
        this.options = options;
        this.initModel();
        this.info = undefined;
        this.solution = {};
    }
    
    isCPSolver() { return true; }

    write(file, text) {
        fs.writeFileSync(file, text, function (err) { if (err) throw err; });
    }
    
    solving(proc) {
        return new Promise((resolve, reject) => {
            proc.on('exit', (c, s) => {
                if (c !== 0) {
                    if (c === 124)
                        console.log('Timeout expired!');
                    else
                        console.log('Exit with signal:', s, 'and code:', c);
                    if (this.options.abort)
                        reject(undefined);
                    else
                        resolve();
                } 
                else
                    resolve(this.info);
            });
            proc.stdout.on('data', (data) => {
                const d = String(data);
                if (this.options.debug)
                    console.log(d);
                this.process_output(d.split('\n'));
            });
            proc.stderr.on('data', (data) => { console.error(String(data)) });
        });
    }
    
    converting(proc) {
        return new Promise((resolve, reject) => {
            proc.on('exit', (c, s) => {
                if (c !== 0) {
                    if (c === 124)
                        console.log('Timeout expired!');
                    else
                        console.log('Exit with signal:', s, 'and code:', c);
                    if (this.options.abort)
                        reject(undefined);
                    else
                        resolve();
                } 
                else
                    resolve();
            });
            proc.stderr.on('data', (data) => { console.error(String(data)) });
        });
    }
    
    async runSolver() {
        const opt = this.options;
        if (opt.twoSteps) {
            const m2f = child_process.spawn(
                "timeout", [opt.mzn2fznTimeout, this.mzn2fzn()].concat(
                opt.mzn2fznArgs.concat([opt.mznPath, opt.dznPath])), 
                {detached: true}
            );    
            await this.converting(m2f, opt);
            CP_PID = m2f.pid;
            const fzn = child_process.spawn(
                "timeout", [opt.fznTimeout, this.fzn()].concat(
                opt.fznArgs.concat([opt.fznPath])), {detached: true}
            );
            CP_PID = fzn.pid;
            return await this.solving(fzn, opt);
        }
        else {
            const mzn = child_process.spawn(
                "timeout", [opt.mznTimeout, this.mzn()].concat(
                opt.mznArgs.concat([opt.mznPath, opt.dznPath])),
                {detached: true}
            );
            CP_PID = mzn.pid;
            return await this.solving(mzn, opt);
        }
    }
        
    getSearch(h, vars) {
        switch (h) {
            case "length":
                var t = ""
                for (let v of vars)
                    t += "str_len(REP_" + v + "), ";
                return "::int_search([" + t + "], first_fail, indomain_min, " +
                    "complete)";
            case "typs":
                t = "";
                for (let v of vars)
                    t += "TYP_" + v + ", ";
                return "::int_search([" + t + "], first_fail, indomain_min, " +
                    "complete)";                    
            case "str_def":
                return "::string_default_search([])";            
            case "reps":
                // FIXME: Does not work atm.
                t = "KEYS[0], ";
                for (let v of vars)
                    t += "REP_" + v + ", ";
                return "::string_default_search([" + t + "])";
            case "typ_len":
                t = "";
                for (let v of vars)
                    t += "TYP_" + v + ", str_len(REP_" + v + "), ";
                return "::int_search([" + t + "], first_fail, indomain_min, " +
                    "complete)";
            case "num_len":
                t = "";
                for (let v of vars)
                    t += "(TYP_" + v + " = Num) * str_len(REP_" + v + "), ";
                return "::int_search([" + t + "], first_fail, indomain_min, " +
                    "complete)";
            default:
                return "";                
        }
    }

    async solveSat(vars) {
//        console.log(vars, this.model)
        const decls = this.declareVars(vars);
        let first_get = {}
        for (const v in this.model.FIRST_GET)
            if (first_get[v] === undefined)
                first_get[v] = this.model.FIRST_GET[v];
        const mzn_model = (
            this.model.head + decls + this.model.body + "solve " + 
            this.getSearch(this.options.solve, vars) + " satisfy;\n"
        );
        const dzn_data = "N_LOCS = " + (vars.size + this.model.N_LOCS) + 
                         ";\nN_EXPL_PROPS = " + this.model.N_EXPL_PROPS + 
                         ";\nN_IMPL_PROPS = " + this.model.N_IMPL_PROPS + ";\n"
        this.write(this.options.mznPath, mzn_model); 
        this.write(this.options.dznPath, dzn_data);
        if (this.options.debug) {
            const c = child_process.spawnSync(
                "cat", [this.options.mznPath, this.options.dznPath]
            )
            console.log(String(c.stdout))
        }
        const rs = this.runSolver();
        for (const v in this.solution)
            this.solution[v].first_get = first_get[v] + this.model.N_IMPL_PROPS;
        return rs;
    }
    
    initModel() {
        this.model = {
            "head":
                "include \"javascript.mzn\";\n" + 
                "include \"alldifferent_except_0.mzn\";\n" +
                "int: N_LOCS;\nint: N_IMPL_PROPS;\nint: N_EXPL_PROPS;\n" +
                "array[0..N_PROPS] of var 0..N_LOCS: LOCS;\n" + 
                "array[0..N_PROPS] of var string: KEYS;\n" +
                "array[0..N_PROPS] of var JSType: TYPS;\n" +
                "array[0..N_PROPS] of var string: REPS;\n" +
                "array[0..N_PROPS] of var 0..N_LOCS: REFS;\n",
            "body": "",
            "N_LOCS": 0,
            "N_WRITES": 0,
            "N_IMPL_PROPS": 0, 
            "N_EXPL_PROPS": 0,
            "FIRST_GET": {}
        }
    }
    
    addConstraint(cons) {
        addMiniZincConstraint(cons, this.model);
    }
    
    min_dom(dom) {
        return dom[0] == '[' ? dom.slice(1, dom.indexOf(".."))
                             : dom.slice(1, dom.indexOf(","));
    }
    
    process_output(data) {
//        console.log(data)
        for (let i in data) {
            const line = data[i];
            const j = line.indexOf(' = ');
            if (j !== -1) {
                // array
                if (line[j - 1] === "S") {
                    const id = line.slice(0, j);
                    // FIXME: Workaround for not-fixed integer var. arrays.
                    if ((line.indexOf("..") != -1 || line.indexOf("{") != -1)
                    && (id === "TYPS" || id === "LOCS" || id === "REFS")) {
                      let l = line.slice(line.indexOf('['), line.length - 2)
                      l = eval('[' + l.replace(/\.\./g, ".").
                          replace(/\[|\]|{|}/g, "") + ']')
                      if (l.length > 0) {
                          for (let i in l)
                              l[i] = Math.floor(l[i])
                          this.solution[id] = l
                      }
                      continue;
                    }
                    const val = id === "LOCS" || id === "REFS"
                        ? eval(line.slice(line.indexOf('['), line.length - 2))
                        // FIXME: Workaround, FlatZinc output needs to be fixed!
                        : eval(('["' + line.slice(
                            line.indexOf('[') + 1, line.length - 3) + '"]')
                            .replace(/, /g, '" , "'));       
                    this.solution[id] = val; 
                    continue;
                }
                const pref = line.slice(0, 3);
                const id = "var" + line[j - 1];
                const val = 
                    pref !== "REP" && 
                    (line.indexOf("[") != -1 || line.indexOf("{") != -1)
                    ? this.min_dom(line.slice(j + 3, line.length - 1))
                    : line.slice(j + 3, line.length - 1);
                if (!this.solution[id])
                    this.solution[id] = {"TYP": null, "REP": null, "LOC": null};
//                console.log(id, pref, val);
                this.solution[id][pref] = val;
            }
            else if (line.includes('---------')) {
                this.info = "sat";
                return;
            }
            else if (line.includes('=====UNSATISFIABLE=====')) {
                this.info = "unsat";
                return;
            }
        }        
    }    
    
    declareVars(vars) {
        let decls = "";
        let vlist =  "";
        for (let v of vars) {
            vlist += "LOC_" + v + ", ";
            const t = "TYP_" + v;
            const r = "REP_" + v;
            const l = "LOC_" + v;
            decls += "var JSType: " + t + ";\nvar string: " + r
                  + ";\nvar 0..N_LOCS: " + l + ";\nconstraint js_var(" + t 
                  + ", " + r + ", " + l + ");\n";
        }
        return decls + "constraint alldifferent_except_0([" + vlist + "]);\n"
    };
    
    pop(n) {
        this.initModel();
    }

    getSolution() {
//        console.log(this.solution)
        return this.solution
    }
    
    close() {
//        console.log("Solver closed")
    }

};

function toObj(typ, loc, solution, first_get) {
    let obj;
    switch (typ) {
        case 6:
           obj = new Array
        case 7:
           obj = new Function
        case 8:
           obj = new Object    
    }
    for (let i = 0; i < solution["LOCS"].length && i <= first_get; ++i)
        if (solution["LOCS"][i] === loc) { 
            const typ = solution["TYPS"][i]; 
            const ref = solution["REFS"][i];
            if (typ <= 5)
                obj[solution["KEYS"][i]] = toVal(typ, solution["REPS"][i])
            else
                obj[solution["KEYS"][i]] = toObj(typ, ref, solution);
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
            return rep === "true"
        case "Num":
            return Number(rep);
        case "Str":
            return rep;
        default:
            console.error("Undefined type! Assuming " + rep)
            return rep; //FIXME: Probable MiniZinc bug in the output!
//            throw new Error("Undefined type");
    }
}

function parseSolution(solution) {
    let model = {}
//    console.log(solution)
    for (let v in solution)
        if (v.startsWith("var")) {
            const typ = Number(solution[v].TYP);
            const loc = Number(solution[v].LOC);
            if (typ <= 5)
                model[v] = toVal(typ, solution[v].REP);
            else
                model[v] = toObj(typ, loc, solution, solution[v].first_get);
//            console.log(v, model[v]);
        }
    return model;
}

exports.parseSolution = parseSolution;
exports.get_cp_pid = get_cp_pid;


