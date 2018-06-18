"use strict";

const fs = require("fs");

const _ = require("lodash");

const sexpr = require("./sexpr");

const { TypeConstraint } = require("./constraint");

const { toMZNConstraint } = require("./mzn-constraint");

const child_process = require("child_process");

const JSTypes = ["Null", "Undef", "Bool", "Num", "Str", "ActiveXObject", "Array", "ArrayBuffer", "Boolean", "DataView", "Date", "Debug", "Enumerator", "Error", "Float32Array", "Float64Array", "Function", "Global", "Int8Array", "Int16Array", "Int32Array", "Intl_Collator", "Intl_DateTimeFormat", "Intl_NumberFormat", "JSON", "Map", "Math", "Number", "Object", "Promise", "Proxy", "Reflect", "RegExp", "Expression", "Set", "String", "Symbol", "Uint8Array", "Uint8ClampedArray", "Uint16Array", "Uint32Array", "VBArray", "WeakMap", "WeakSet", "WinRTError"]

exports.CPSolver = class CPSolver {

    constructor(cmd, model, data) {
        this.cmd = cmd;
        this.mzn = model;
        this.dzn = data;
        this.mzn_buffer = [
            "include \"javascript.mzn\"", "int: NUM_LOCS", "int: NUM_WRITES",
            "int: NUM_BUILTIN"
        ];
        this.builtins = ""
        this.solution = {};
        this.NUM_LOCS = 0;
        this.NUM_WRITES = 0;
        this.NUM_BUILTIN = 0;
    }
    
    isCPSolver() { return true; }

    write(file, text) {
        fs.writeFileSync(file, text, function (err) { if (err) throw err; });
    }

    solveSat() {
        // FIXME: Temporary workaround for dzn.
        this.write(
            this.dzn, "NUM_LOCS = " + this.NUM_LOCS
                 + ";\nNUM_WRITES = " + this.NUM_WRITES
                 + ";\nNUM_BUILTIN = " + this.NUM_BUILTIN + ";\n"
        );
        this.write(
            this.mzn, this.builtins + this.mzn_buffer.join(";\n") + ";\nsolve satisfy;\n"
        );
//        console.log("% Model")
//        const c = child_process.spawnSync("cat", [this.mzn, this.dzn]);
//        console.log(String(c.stdout))
        const res = child_process.spawnSync(this.cmd, [this.mzn, this.dzn]);
        if (res.status != 0) {
            console.log(String(res.stderr))
            return undefined
        }
        this.mzn_buffer.push("% =====SOLVED=====");
        this.builtins = ""
        this.NUM_LOCS = 0;
        this.NUM_WRITES = 0;
        this.NUM_BUILTIN = 0;
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
    
    declareVar(name, type) {
        var decl;
        const t = "TYP_" + name
        const r = "REP_" + name
        const l = "LOC_" + name
        if (type) {
            this.mzn_buffer.push("var " + type.toJSType() + t);
            if (type.has(Type.OBJECT))
                this.NUM_LOCS++;
        }
        else {
            this.mzn_buffer.push("var JSType: " + t);
            this.NUM_LOCS++;
        }
        this.mzn_buffer.push("var string: "  + r);
        this.mzn_buffer.push("var 0..NUM_LOCS: " + l);
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
        console.log(solution[v])
        console.log(JSTypes[Number(solution[v].TYP) - 1])
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
               sol = solution[v].REP;
               break;                                                                    
        }
        model[v] = sol;
    }
    return model;
}

exports.parseSolution = parseSolution;

