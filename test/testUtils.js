/* global before */

const child_process = require("child_process");
const process = require("process");

exports.testCVC4 = function() {
    const cvc4Path = process.env.CVC4_PATH || "cvc4";
    before(function() {
        try {
            child_process.execFileSync(cvc4Path, ["--version"], { encoding: "utf8" });
        } catch (e) {
            if (e.code === "ENOENT") {
                console.error(`ENOENT: could not find CVC4 at '${cvc4Path}'`);
            } else {
                throw e;
            }
            this.skip();
        }
    });
    return cvc4Path;
};

exports.testZ3 = function() {
    const z3Path = process.env.Z3_PATH || "z3";
    before(function() {
        try {
            child_process.execFileSync(z3Path, ["-version"], { encoding: "utf8" });
        } catch (e) {
            if (e.code === "ENOENT") {
                console.error(`ENOENT: could not find Z3 at '${z3Path}'`);
            } else {
                throw e;
            }
            this.skip();
        }
    });
    return z3Path;
};
