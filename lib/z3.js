const child_process = require("child_process");

const smt = require("./smt");

class Z3 extends smt.Solver {
    constructor(solverPath) {
        const z3 = child_process.spawn(solverPath, ["-smt2", "-in", "TRACE=true"]);
        super(z3);
    }
}

module.exports = Z3;
