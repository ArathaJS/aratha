const child_process = require("child_process");

const smt = require("./smt");

class CVC4 extends smt.Solver {
    constructor(solverPath, logic) {
        const cvc4 = child_process.spawn(solverPath, ["--lang=smt2", "--strings-exp", "--incremental", "-"]);
        super(cvc4);
        this._send(["set-logic", logic]);
    }
}

module.exports = CVC4;
