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

function runScript(scriptPath, solverName) {
    if (activeChild) {
        throw new Error("analysis already running");
    }
    console.log("running", scriptPath, "on", solverName);
    const analysis = child_process.spawn(
        "node",
        ["../src/js/commands/jalangi.js", "--analysis", "./", scriptPath],
        {
            stdio: "inherit",
            env: {
                SMT_SOLVER: solverName,
                CVC4_PATH: process.env.CVC4_PATH,
                Z3_PATH: process.env.Z3_PATH,
                ANALYSIS_TIMEOUT: analysisTimeout
            }
        }
    );
    activeChild = analysis;
    let analysisTimer = null;
    if (analysisTimeout > 0) {
        analysisTimer = setTimeout(
            () => analysis.kill(),
            (analysisTimeout + 1) * 1000); // give a chance to exit gracefully
    }
    return new Promise((resolve, reject) => {
        analysis.on("exit", (exitCode, signal) => {
            activeChild = null;
            clearTimeout(analysisTimer);
            resolve(exitCode !== null ? exitCode : signal);
        });
    });
}

async function main() {
    for(let scriptPath of scripts) {
        for(let solverName of solvers) {
            if (receivedSigint) {
                break;
            }

            const start = process.hrtime();
            const status = await runScript(scriptPath, solverName);
            const end = process.hrtime();
            if (status !== 0) {
                if (typeof status === "number") {
                    console.log("analysis process terminated with exit code", status);
                } else {
                    console.log("analysis process received signal", status);
                }
            }

            const scriptName = path.basename(scriptPath, ".js");

            try {
                let rawLog = fs.readFileSync("inputlog.json", {encoding: "utf8"}).trim();
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
                    timeElapsed: (end[0] - start[0]) + (end[1] - start[1]) / 1e9
                });
            } catch(e) {
                console.error("exception:", e);
            }

            const logName = scriptName + "." + solverName;
            fs.renameSync("inputlog.json", logName + ".inputlog.json");
            fs.renameSync("solver_commands.smt2", logName + ".solver_commands.smt2");
        }
    }
    console.log("Timings")
    console.log("-------")
    console.log(["Solver", "Script", "# inputs", "# unique inputs", "Time"].join("\t"));
    timings.forEach((timing) => {
        console.log([timing.solverName, timing.scriptName,, timing.numCases, timing.numUniqueCases, timing.timeElapsed].join("\t"));
    });
}

main().catch((e) => {
    console.error("uncaught error:", e);
});
