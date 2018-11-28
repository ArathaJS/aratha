const child_process = require("child_process");

const { SMTSolver } = require("./smt");

//"smt.string_solver=z3str3"

class Z3 extends SMTSolver {
    constructor(solverPath) {
        const z3 = child_process.spawn(solverPath, ["-smt2", "model_compress=false", "-in"]);
        super(z3);
    }
}

module.exports = Z3;
