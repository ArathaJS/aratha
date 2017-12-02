const fs = require("fs");
const process = require("process");
const child_process = require("child_process");
const path = require("path");

const _ = require("lodash");

const scripts = process.argv.slice(2).filter((s) => s.indexOf("_jalangi_") === -1);
const settings = process.env.SETTINGS || "";
const logdir = process.env.LOGDIR || "./";

scripts.forEach((scriptPath) => {
	const scriptName = path.basename(scriptPath, ".js");
    const inputFilename = logdir + scriptName + (settings.length > 0 ? "." + settings : "") + ".inputlog.json";

    let rawLog = fs.readFileSync(inputFilename, {encoding: "utf8"}).trim();
    if (!rawLog.endsWith("]"))
        rawLog += "]";
    const inputs = JSON.parse(rawLog).map((x, i) => ({idx: i, input: x}));
    const uniqueInputs = _.uniqWith(inputs, (a, b) => _.isEqual(a.input, b.input));
    for (let el of uniqueInputs) {
        console.log("replaying " + el.idx);
        child_process.spawnSync("node", ["-r", "./lib/input-reader.js", scriptPath], {env: {INPUT_FILE: inputFilename, INPUT_IDX: el.idx.toString()}, stdio: "inherit"});
    }
});
