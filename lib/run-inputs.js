const fs = require("fs");
const process = require("process");
const child_process = require("child_process");

const scripts = process.argv.slice(2);
const scriptPath = process.argv[2];
const timings = [];

scripts.forEach((scriptPath) => {
	const start = process.hrtime();
    child_process.spawnSync("node", ["../src/js/commands/jalangi.js", "--analysis", "./", scriptPath], {stdio: "inherit"});
    const end = process.hrtime();
    console.log("analysis ended");
    const n = JSON.parse(fs.readFileSync("inputlog.json")).length;
    timings.push({
    	scriptPath: scriptPath,
    	numCases: n,
    	timeElapsed: (end[0] - start[0]) + (end[1] - start[1]) / 1e9
    });
    for (var i = 0; i < n; i++) {
        console.log("replaying " + i);
        child_process.spawnSync("node", ["-r", "./lib/input-reader.js", scriptPath], {env: {INPUT_IDX: i.toString()}, stdio: "inherit"});
    }
    fs.renameSync("inputlog.json", scriptPath + ".inputlog.json");
});

console.log("Timings")
console.log("-------")
console.log("Script\t\t\t\tNumber of cases\tTime\t");
timings.forEach((timing) => {
	console.log(timing.scriptPath + "\t" + timing.numCases + "\t" + timing.timeElapsed);
});
