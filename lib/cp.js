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
            "\";\nint: MIN_LOC;\nint: N_LOCS;\nint: N_IMPL_PROPS;"+ 
            "\nint: N_EXPL_PROPS;\n";
        this.mznHead = "";
        this.models = [];
        this.solution = {};
        this.builtin_vars = {};
        this.proc = undefined; 
    }
    
    isCPSolver() { return true; }

    write(file, text) {
        fs.writeFileSync(file, text, function (err) { if (err) throw err; });
    }
    
    checkRes(res, t, a) {
        if (res.status !== 0) {
            //console.log(res)
            process.kill(-res.pid);
            if (res.error.code === 'ETIMEDOUT')
                console.log("Timeout (" + t + " seconds) expired!");
            else
                console.log(String(res.stderr));
            if (a)
                throw new Error("Execution aborted.");
            return false
        }
        return true;
    }
    
    
    onExit(proc, opt) {
        return new Promise((resolve, reject) => {
            proc.on('exit', (c, s) => {
                console.log('Exit with signal:', s, 'and code:', c);
                if (c !== 0 && opt.abort)
                    reject();
                else
                    resolve();
            });
            proc.stdout.on('data', (data) => { console.log(String(data)) });
            proc.stderr.on('data', (data) => { console.error(String(data)) });
        });
    }
    
    async runSolver(opt) {
        if (opt.twoSteps) {
            var res = child_process.spawnSync(this.mzn2fzn(),
                opt.mzn2fznArgs.concat([opt.mznPath, opt.dznPath]),
                {timeout: opt.mzn2fznTimeout * 1000, detached: true}                
            );
            if (!this.checkRes(res, opt.mzn2fznTimeout, opt.abort))
                return undefined;
            const fzn = child_process.spawn(
                this.fzn(), opt.fznArgs.concat([opt.fznPath]), {detached: true}
            );
            setTimeout(() => { process.kill(-fzn.pid) }, 1000 * opt.fznTimeout);
            await this.onExit(fzn, opt)
        }
        else {
            res = child_process.spawnSync(this.mzn(),
                opt.mznArgs.concat([opt.mznPath]),
                {timeout: opt.mznTimeout * 1000, detached: true}
            );
            if (!this.checkRes(res, opt.mznTimeout, opt.abort))
                return undefined;
        }
        if (opt.debug)
            console.log(String(res.stdout));
        return res;
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
            case "typ_len":
                t = "";
                for (let v of vars)
                    t += "TYP_" + v + ", str_len(REP_" + v + "), ";
                return "::int_search([" + t + "], first_fail, indomain_min, " +
                    "complete)";
            default:
                return "";                
        }
    }

    solveSat(vars, opt) {
//        console.log(vars, this.models)
        const decls = this.declareVars(vars);
        let locs = vars.size, eprops = 0, iprops = 0, min_loc = 1, model = "";
        for (const mi of this.models) {
            model += mi.body;
            locs += mi.N_LOCS;
            iprops += mi.N_IMPL_PROPS;
            eprops += mi.N_EXPL_PROPS;
            min_loc += mi.MIN_LOC;
        }
        const mzn_model = (
            this.preamble + decls + model + "solve " + 
            this.getSearch(opt.solve, vars) + " satisfy;\n"
        );
        const dzn_data = "N_LOCS = " + locs + ";\nN_EXPL_PROPS = " + eprops + 
            ";\nN_IMPL_PROPS = " + iprops + ";\nMIN_LOC = " + min_loc + ";\n"
        this.write(opt.mznPath, mzn_model); 
        this.write(opt.dznPath, dzn_data);
        if (opt.debug) {
            const c = child_process.spawnSync("cat", [opt.mznPath, opt.dznPath])
            console.log(String(c.stdout))
        }
        const res = this.runSolver(opt);
        if (!res)
            return undefined;
        return this.process_output(String(res.stdout).split('\n'))
    }
    
    newModel() {
        return {
            "body": "",
            "N_LOCS": 0, "MIN_LOC": 0, "N_IMPL_PROPS": 0, "N_EXPL_PROPS": 0
        }
    }
    
    addConstraint(cons) {
        let m = this.newModel();
        let n_impl = 0;
        for (let mi of this.models)
          n_impl += mi.N_IMPL_PROPS;
        this.models.push(toMZNConstraint(
            cons, m, this.models.length, this.builtin_vars, n_impl
        ));
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
            else if (line.includes('---------'))
                return "sat";
            else if (line.includes('=====UNSATISFIABLE====='))
                return "unsat";
            else
                return "unknown"
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
            decls += "var JSType: " + t + ";\nvar string: " + r + 
            ";\nvar {0} union MIN_LOC..N_LOCS: " + l + 
            ";\nconstraint js_var(" + t + ", " + r + ", " + l + ");\n";
        }
        return decls + "constraint alldifferent_except_0([" + vlist + "]);\n"
    };
    
    pop(n) {
//        console.log("Pop " + n, this.models);
        const m = this.models.length - n;
        for (const [v, i] of Object.entries(this.builtin_vars))
            if (i >= m)
                delete this.builtin_vars[v];
        this.models = this.models.slice(0, m);
//        console.log(this.models, this.models.length);
    }

    getSolution() {
//        console.log(this.solution)
        return this.solution
    }
    
    close() {
        if (this.proc)
            this.proc.kill()
        console.log("Solver closed")
    }

};

function toObj(typ, loc, solution) {
    let obj;
    switch (typ) {
        case 6:
           obj = new Array
        case 7:
           obj = new Function
        case 8:
           obj = new Object    
    }
    for (let i = 0; i < solution["LOCS"].length; ++i)
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
            throw new Error("Undefined type", typ);
    }
}

function parseSolution(solution) {
    let model = {}
    for (let v in solution)
        if (v.startsWith("var")) {
            const typ = Number(solution[v].TYP);
            const loc = Number(solution[v].LOC);
            if (typ <= 5)
                model[v] = toVal(typ, solution[v].REP);
            else
                model[v] = toObj(typ, loc, solution);
//            console.log(v, model[v]);
        }
    return model;
}

exports.parseSolution = parseSolution;

