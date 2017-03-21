const child_process = require("child_process");
const fs = require("fs");

const smt = require("./smt");

class Z3 extends smt.Solver {
    constructor(solver_path, theory_path) {
        const z3 = child_process.spawn(solver_path, ["-smt2", "-in"]);
        super(z3);
        z3.stdin.write(fs.readFileSync(theory_path));
    }
}

module.exports = Z3;
