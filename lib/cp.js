"use strict";

const assert = require("assert");

const fs = require("fs");

const Type = require("./type");

const _ = require("lodash");

const sexpr = require("./sexpr");

const { addMiniZincConstraint } = require("./mzn-constraint");

const child_process = require("child_process");

const JSTypes = [
    "Null", "Undef", "Bool", "Num", "Str", "Object", "Array", "Function"
]

var CP_PID = null;
function get_cp_pid() { return CP_PID };

exports.CPSolver = class CPSolver {

    constructor(options) {
        this.options = options;
        this.initModel();
    }
    
    isCPSolver() { return true; }

    write(file, text) {
        fs.writeFileSync(file, text, function (err) { if (err) throw err; });
    }
    
    append(file, text) {
        fs.appendFileSync(file, text, function (err) { if (err) throw err; });
    }
    
    solving(proc) {
        return new Promise((resolve, reject) => {
            proc.on('exit', (c, s) => {
                if (c !== 0) {
                    if (c === 124) {
                        console.log('Timeout expired!');
                        if (this.options.dumpTimeout) {
                            const shell = require('shelljs');
                            shell.exec(
                                "cat " + this.options.mznPath + " " + 
                                this.options.dznPath + " >> " + 
                                this.options.dumpTimeout
                            )
                            shell.exec(
                                'echo "==========" >> ' + this.options.dumpTimeout
                            )
                        }
                    }
                    // FIXME: fzn-gecode can exit with code 1 even when a 
                    //        solution is actually found!
//                    else
//                        console.log('Exit with signal:', s, 'and code:', c);
                    if (this.options.abort)
                        reject("Aborted");
                    else
                        resolve(this.info);
                }
                else
                    resolve(this.info);
            });
            proc.stdout.on('data', (data) => {
                const d = data.toString("binary");
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
                        reject("Aborted");
                    else
                        resolve();
                } 
                else
                    resolve();
            });
            proc.stderr.on('data', (data) => { console.error(String(data)) });
        });
    }
    
    async runSolver(new_cons) {
        if (new_cons)
            this.append(this.options.mznPath, new_cons);
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
        
    getSearch(h, vars, n) {
        switch (h) {
            case "length":
                var t = ""
                for (let v of vars)
                    if (v.startsWith('var'))
                        t += "str_len(SVAL_" + v + "), ";
                return "::int_search([" + t + "], first_fail, indomain_min, " +
                    "complete)";
            case "typs":
                t = "";
                for (let v of vars)
                    if (v.startsWith('var'))
                        t += "TYPE_" + v + ", ";
                return "::int_search([" + t + "], first_fail, indomain_min, " +
                    "complete)";                    
            case "str_def":
                return "::string_default_search([])";            
            case "reps":
                // FIXME: Does not work atm.
                t = "P_NAMES[0], ";
                for (let v of vars)
                    if (v.startsWith('var'))
                        t += "SVAL_" + v + ", ";
                return "::string_default_search([" + t + "])";
            case "type_len":
                t = "";
                for (let v of vars)
                    if (v.startsWith('var'))
                        t += "TYPE_" + v + ", str_len(SVAL_" + v + "), ";
                return "::int_search([" + t + "], first_fail, indomain_min, " +
                    "complete)";
            case "num_len":
                t = "";
                for (let v of vars)
                    if (v.startsWith('var'))
                        t += "(TYPE_" + v + " = Num) * str_len(SVAL_" + v + "), ";
                return "::int_search([" + t + "], first_fail, indomain_min, " +
                    "complete)";
            case "nobj_len":
                t = "";
                for (let v of vars)
                    if (v.startsWith('var'))
                        t += "(TYPE_" + v + " * ((TYPE_" + v + " < Object) * str_len(SVAL_" + v + "))), ";
                return "::int_search([" + t + "], first_fail, indomain_min, complete)";
//            case "symb":
//                t = "::string_default_search([]) ::int_search([";
//                for (let i = 1; i <= n; ++i) 
//                    t += "O_ADDRS[" + i + "], P_TYPES[" + i + "], P_ADDRS[" + i + "], ";
//                t += "], first_fail, indomain_min, complete)";
//                return t;
            default:
                return "";                
        }
    }

    async solveSat(vars) {
        // console.log(vars, this.model)
        const decls = this.declareVars(vars);
        const n_props = this.model.N_IMPL_PROPS + this.model.N_EXPL_PROPS;
        const mzn_model = (
            this.model.head + decls + this.model.body + "solve " + 
            this.getSearch(this.options.solve, vars, n_props) + " satisfy;\n"
        );
        const dzn_data = "N_ADDRS = " + (vars.size + this.model.N_ADDRS) + 
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
        return rs;
    }
    
    initModel() {
        this.model = {
            "head":
                "include \"javascript.mzn\";\n" + 
                "include \"alldifferent_except_0.mzn\";\n" +
                "int: N_ADDRS;\nint: N_IMPL_PROPS;\nint: N_EXPL_PROPS;\n" +
                "array[0..N_PROPS] of var 0..N_ADDRS: O_ADDRS;\n" + 
                "array[0..N_PROPS] of var string: P_NAMES;\n" +
                "array[0..N_PROPS] of var JSType: P_TYPES;\n" +
                "array[0..N_PROPS] of var string: P_SVALS;\n" +
                "array[0..N_PROPS] of var 0..N_ADDRS: P_ADDRS;\n",
            "body": "",
            "N_ADDRS": 0,
            "N_WRITES": 0,
            "N_IMPL_PROPS": 0, 
            "N_EXPL_PROPS": 0,
            "FIRST_GET": {},
            "REGEX_ID": new Set(),
            "SMT_CONS": new Set(),
            "TMP_ADDRS": [],
            "MAYBE_ARRAY": false
        }
        this.info = undefined;
        this.solution = {};
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
                    && (id === "P_TYPES" || id === "O_ADDRS" || id === "P_ADDRS")) {
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
                    const val = id === "O_ADDRS" || id === "P_ADDRS"
                        ? eval(line.slice(line.indexOf('['), line.length - 2))
                        // FIXME: Workaround, FlatZinc output needs to be fixed!
                        : eval(('["' + line.slice(
                            line.indexOf('[') + 1, line.length - 3) + '"]')
                            .replace(/, /g, '" , "'));       
                    this.solution[id] = val; 
                    continue;
                }
                const pref = line.slice(0, 4);
                const id = line.slice(5, line.indexOf(" = "));
                let val = 
                    pref !== "SVAL" && 
                    (line.indexOf("[") != -1 || line.indexOf("{") != -1)
                    ? this.min_dom(line.slice(j + 3, line.length - 1))
                    : line.slice(j + 3, line.length - 1);
                if (val === "" && line.indexOf(";") === -1)
                  val = '\n';
                if (!this.solution[id])
                    this.solution[id] = {
                        "TYPE": null, "SVAL": null, "ADDR": null
                    };
//                console.log(id, pref, val);
                this.solution[id][pref] = val;
            }
            else if (line.includes('---------')) {
                this.info = "sat";
                for (const v in this.solution)
                    if (/var\d/.test(v))
                        this.solution[v].first_get = 
                            this.model.FIRST_GET[v] + this.model.N_IMPL_PROPS;
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
            vlist  += "ADDR_" + v + ", ";
            const t = "TYPE_" + v;
            const r = "SVAL_" + v;
            const l = "ADDR_" + v;
            const a = this.model.MAYBE_ARRAY ? "Array" : "";
            decls += "var {Null, Undef, Bool, Num, Str, Object, " + a + "}: " + t 
                  + ";\nvar string: " + r
                  + ";\nvar 0..N_ADDRS: " + l + ";\nconstraint js_var(" + t 
                  + ", " + r + ", " + l + ");\n";
        }
        vlist = vlist.concat(this.model.TMP_ADDRS);
        return decls + "constraint alldifferent_except_0([" + vlist + "]);\n"
    };
    
    pop(n) {
        assert (n == 1);
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

function toObj(type, sval, addr, solution, first_get) {
    let obj;
    switch (type) {
        case 6:
            obj = new Object;
            break; 
        case 7:
            obj = [];
            break; 
        case 8:
        default:
            obj = new Object;
            break;    
    }
    let l = Infinity;
    for (let i = 0; i < solution["O_ADDRS"].length && i <= first_get; ++i) {
        if (solution["O_ADDRS"][i] === addr) { 
            const type_i = solution["P_TYPES"][i];
            const sval_i = solution["P_SVALS"][i];
            const addr_i = solution["P_ADDRS"][i];
            obj[solution["P_NAMES"][i]] = (type_i <= 5) ?
                toVal(type_i, solution["P_SVALS"][i]) :                
                toObj(type_i, sval_i, addr_i, solution, first_get);
            if (obj instanceof Array && solution["P_NAMES"] === "length")
                l = +sval_i;
        }
    }
//    console.log(addr, obj)
    if (obj instanceof Array)
        obj.length = Math.min(l, Math.floor((sval.length + 1) / 2));
    return obj;
}

function toVal(type, sval) {
    switch (JSTypes[Number(type) - 1]) {
        case "Undef":
            return undefined;
        case "Null":
            return null;
        case "Bool":
            return sval === "true"
        case "Num":
            return Number(sval);
        case "Str":
            return sval;
        default:
            console.error("Undefined type! Assuming " + sval)
            return sval; //FIXME: Probable MiniZinc output bug!
//            throw new Error("Undefined type");
    }
}

function parseSolution(solution) {
    let model = {}
    for (let v in solution)
        if (v.startsWith("var") || v.startsWith("regex")) {
            const type = Number(solution[v].TYPE);
            const sval = solution[v].SVAL;
            const addr = Number(solution[v].ADDR);
            if (type <= 5)
                model[v] = toVal(type, sval);
            else
                model[v] = toObj(type, sval, addr, solution, solution[v].first_get);
        }
    return model;
}

exports.JSTypes = JSTypes;
exports.parseSolution = parseSolution;
exports.get_cp_pid = get_cp_pid;


