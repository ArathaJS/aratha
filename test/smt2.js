/* global describe context it */

const child_process = require("child_process");
const path = require("path");
const { testCVC4, testZ3 } = require("./testUtils");

describe("running CVC4", function() {
    context("on common.smt2", function() {
        const cvc4Path = testCVC4();
        it("should terminate with no errors", function(done) {
            const filePath = path.resolve(__dirname, "../lib/smt2/common.smt2");
            child_process.execFile(cvc4Path, ["--lang=smt2", "--strings-exp", "--incremental", filePath], done);
        });
    });
});

describe("running Z3", function() {
    context("on common.smt2", function() {
        const z3Path = testZ3();
        it("should terminate with no errors", function(done) {
            const filePath = path.resolve(__dirname, "../lib/smt2/common.smt2");
            child_process.execFile(z3Path, [filePath], done);
        });
    });
});
