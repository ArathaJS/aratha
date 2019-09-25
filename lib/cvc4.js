const child_process = require("child_process");
const { SMTSolver } = require("./smt");

class CVC4 extends SMTSolver {

    constructor(solverPath, logic) {
        const args = [
            "--lang=smt2",
            "--strings-exp",
            "--incremental",
            "--tlimit-per=10000",
            "--strings-guess-model"
        ];
        if (process.env.UNSAT_CORES === "1") {
            args.push("--produce-unsat-cores");
        }
        args.push("-");
        const cvc4 = child_process.spawn(solverPath, args);
        super(cvc4);
        this._send(["set-logic", logic]);
        this.id = "cvc4"
    }
}

module.exports = CVC4;
