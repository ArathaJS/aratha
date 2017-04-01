/* global describe it */

"use strict";

const child_process = require("child_process");
const path = require("path");

const _ = require("lodash");
const glob = require("glob");

describe("the analysis", function() {
    const scriptPath = path.resolve(__dirname, "../../src/js/commands/jalangi.js");
    const examplesDir = path.resolve(__dirname, "examples");
    const analysisDir = path.resolve(__dirname, "../");

    const collator = new Intl.Collator(undefined, {numeric: true, sensitivity: "base"});
    const files = glob.sync("example+([0-9]).js", {nosort: true, cwd: examplesDir, absolute: true});
    files.sort(collator.compare);

    _.forEach(files, function(filePath) {
        const testName = path.basename(filePath, ".js");
        it(`correctly executes ${testName}`, function(done) {
            child_process.execFile("node", [scriptPath, "--analysis", analysisDir, filePath], done);
        });
    });
});
