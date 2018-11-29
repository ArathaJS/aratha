const child_process = require("child_process");

const { SMTSolver } = require("./smt");

class Z3str extends SMTSolver {
    constructor(solverPath) {
        const z3str = child_process.spawn(solverPath, ["-smt2", "smt.string_solver=z3str3", "model_compress=false", "-in"]);
        super(z3str);
    }
}

module.exports = Z3str;
