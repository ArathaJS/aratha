const fs = require("fs");
const process = require("process");
const child_process = require("child_process");
const path = require("path");

const _ = require("lodash");

const scripts = process.argv.slice(2).filter((s) => s.indexOf("_jalangi_") === -1);
const timings = [];

const solvers = process.env.TRY_SOLVERS ? process.env.TRY_SOLVERS.split(",") : [process.env.SMT_SOLVER || "cvc4"];
const analysisTimeout = parseInt(process.env.ANALYSIS_TIMEOUT, 10) || 0;

let activeChild = null;
let receivedSigint = false;

process.on("SIGINT", () => {
    receivedSigint = true;
    console.log("run-inputs: received SIGINT, terminating");
    activeChild.kill();
});

function runScript(scriptPath, solverName, options) {
    if (activeChild) {
        throw new Error("analysis already running");
    }
    console.log("running", scriptPath, "on", solverName);
    const env = {
        PATH: process.env.PATH,
        SMT_SOLVER: solverName,
        UNSAT_CORES: options.unsatCores ? 1 : 0,
        INCREMENTAL: options.incremental ? 1 : 0,
        ANALYSIS_TIMEOUT: analysisTimeout
    };
    if (process.env.CVC4_PATH) {
        env.CVC4_PATH = process.env.CVC4_PATH;
    }
    if (process.env.Z3_PATH) {
        env.Z3_PATH = process.env.Z3_PATH;
    }
    const analysis = child_process.spawn(
        "node", ["../src/js/commands/jalangi.js", "--analysis", "./", scriptPath], {
            stdio: "inherit",
            env: env
        }
    );
    activeChild = analysis;
    let analysisTimer = null;
    if (analysisTimeout > 0) {
        analysisTimer = setTimeout(
            () => analysis.kill(),
            (analysisTimeout + 1) * 1000); // give a chance to exit gracefully
    }
    return new Promise((resolve) => {
        analysis.on("exit", (exitCode, signal) => {
            activeChild = null;
            clearTimeout(analysisTimer);
            resolve(exitCode !== null ? exitCode : signal);
        });
    });
}

function possibleOptions() {
    const alloptions = [];
    for (let i = 0; i < 2; ++i) {
        for (let j = 0; j < 2; ++j) {
            alloptions.push({
                unsatCores: i,
                incremental: j
            });
        }
    }
    return alloptions;
}

function printTimings() {
    console.log("Timings");
    console.log("-------");
    console.log(["Program", "Solver", "Unsat cores?", "Incremental?", "# inputs", "# unique inputs", "Time"].join("\t"));
    timings.forEach((timing) => {
        console.log([
            timing.scriptName,
            timing.solverName,
            timing.options.unsatCores ? "y" : "n",
            timing.options.incremental ? "y" : "n",
            timing.numCases,
            timing.numUniqueCases,
            timing.timeElapsed
        ].join("\t"));
    });
}

async function main() {
    const alloptions = possibleOptions();
    for (const scriptPath of scripts) {
        for (const solverName of solvers) {
            for (const options of alloptions) {
                if (receivedSigint) {
                    return;
                }

                const start = process.hrtime();
                const status = await runScript(scriptPath, solverName, options);
                const elapsed = process.hrtime(start);
                if (status !== 0) {
                    if (typeof status === "number") {
                        console.log("analysis process terminated with exit code", status);
                    } else {
                        console.log("analysis process received signal", status);
                    }
                }

                const scriptName = path.basename(scriptPath, ".js");

                try {
                    let rawLog = fs.readFileSync("inputlog.json", { encoding: "utf8" }).trim();
                    if (!rawLog.endsWith("]"))
                        rawLog += "]";
                    const inputs = JSON.parse(rawLog);
                    const uniqueInputs = _.uniqWith(inputs, _.isEqual);

                    timings.push({
                        scriptName: scriptName,
                        solverName: solverName,
                        scriptPath: scriptPath,
                        numCases: inputs.length,
                        numUniqueCases: uniqueInputs.length,
                        options: options,
                        timeElapsed: elapsed[0] + elapsed[1] / 1e9
                    });
                } catch (e) {
                    console.error("exception:", e);
                }

                const logName = [
                    scriptName,
                    solverName,
                    options.unsatCores ? "uc" : "no-uc",
                    options.incremental ? "inc" : "no-inc"
                ].join(".");
                fs.renameSync("inputlog.json", logName + ".inputlog.json");
                fs.renameSync("solver_commands.smt2", logName + ".solver_commands.smt2");

            }
        }
    }
}

main().then(() => {
    printTimings();
    console.log("run-inputs: finished");
}).catch((e) => {
    printTimings();
    console.error("run-inputs: uncaught error:", e);
});
