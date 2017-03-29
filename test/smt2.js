/* global describe context it */

const child_process = require("child_process");
const path = require("path");
const process = require("process");

const SMT_SOLVER = process.env.SMT_SOLVER;

describe("running an SMT-LIB 2 solver", function() {
    context("on ecmascript.smt2", function() {
        it("should terminate with no errors", function(done) {
            if (SMT_SOLVER !== undefined) {
                const filePath = path.resolve(__dirname, "../lib/ecmascript.smt2");
                child_process.execFile(SMT_SOLVER, [filePath], done);
            } else {
                this.skip();
            }
        });
    });
});
