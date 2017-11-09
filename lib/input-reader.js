function getInput() {
    const fs = require("fs");
    const process = require("process");

    const n = parseInt(process.env.INPUT_IDX, 10);
    if (!isFinite(n) || n < 0) {
        throw new Error("invalid INPUT_IDX " + process.env.INPUT_IDX);
    }
    const allInputs = JSON.parse(fs.readFileSync(process.env.INPUT_FILE || "inputlog.json"));
    if (n >= allInputs.length) {
        throw new Error("INPUT_IDX = " + n + " out of range for array of length" + allInputs.length);
    }
    return allInputs[n];
}

let i = 0;
const inputs = getInput();
global.J$ = {
    readInput: function() {
        return inputs["var" + i++];
    }
};
