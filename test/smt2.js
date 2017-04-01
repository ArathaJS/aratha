/* global describe context it */

const child_process = require("child_process");
const path = require("path");
const process = require("process");

const CVC4_PATH = process.env.CVC4_PATH;

describe("running CVC4", function() {
    context("on common.smt2", function() {
        it("should terminate with no errors", function(done) {
            if (CVC4_PATH !== undefined) {
                const filePath = path.resolve(__dirname, "../lib/smt2/common.smt2");
                child_process.execFile(CVC4_PATH, ["--lang=smt2", "--strings-exp", "--incremental", filePath], done);
            } else {
                this.skip();
            }
        });
    });
});

const Z3_PATH = process.env.Z3_PATH;

describe("running Z3", function() {
    context("on common.smt2", function() {
        it("should terminate with no errors", function(done) {
            if (Z3_PATH !== undefined) {
                const filePath = path.resolve(__dirname, "../lib/smt2/common.smt2");
                child_process.execFile(Z3_PATH, [filePath], done);
            } else {
                this.skip();
            }
        });
    });
});
