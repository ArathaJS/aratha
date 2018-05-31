const child_process = require("child_process");

const { SMTSolver } = require("./smt");

class CVC4 extends SMTSolver {
    constructor(solverPath, logic) {
        const cvc4 = child_process.spawn(solverPath, [
            "--lang=smt2", "--strings-exp", "--incremental",
            "--tlimit-per=30000", "--strings-guess-model", "-"
        ]);
        super(cvc4);
        this._send(["set-logic", logic]);
    }
}

module.exports = CVC4;
