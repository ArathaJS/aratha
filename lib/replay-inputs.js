const fs = require("fs");
const process = require("process");
const child_process = require("child_process");
const path = require("path");

const scripts = process.argv.slice(2);

scripts.forEach((scriptPath) => {
    const inputFilename = path.basename(scriptPath, ".js") + ".inputlog.json";
    const n = JSON.parse(fs.readFileSync(inputFilename)).length;
    for (var i = 0; i < n; i++) {
        console.log("replaying " + i);
        child_process.spawnSync("node", ["-r", "./lib/input-reader.js", scriptPath], {env: {INPUT_FILE: inputFilename, INPUT_IDX: i.toString()}, stdio: "inherit"});
    }
});
