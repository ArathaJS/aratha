const child_process = require("child_process");

const { SMTSolver } = require("./smt");

class Z3 extends SMTSolver {
    constructor(solverPath) {
        const z3 = child_process.spawn(solverPath, ["-smt2", "model_compress=false", "-in"]);
        super(z3);
        this.id = "z3";
    }
}

module.exports = Z3;
