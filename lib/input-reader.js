"use strict";

function getInput() {
    const fs = require("fs");
    const process = require("process");

    const n = parseInt(process.env.INPUT_IDX, 10);
    if (!isFinite(n) || n < 0) {
        throw new Error("invalid INPUT_IDX " + process.env.INPUT_IDX);
    }
    let rawLog = fs.readFileSync(process.env.INPUT_FILE || "inputlog.json", { encoding: "utf8" }).trim();
    if (!rawLog.endsWith("]"))
        rawLog += "]";
    const allInputs = JSON.parse(rawLog);
    if (n >= allInputs.length) {
        throw new Error("INPUT_IDX = " + n + " out of range for array of length" + allInputs.length);
    }
    return allInputs[n];
}

let i = 0;
const inputs = getInput();

function getNextInput(default_) {
    const name = "var" + i++;
    if (!inputs.hasOwnProperty(name))
        return default_;
    return inputs[name];
}

global.J$ = {
    readInput: function() {
        return getNextInput(undefined);
    },
    readString: function() {
        return getNextInput("");
    },
    readNumber: function() {
        return getNextInput(0);
    },
    readBoolean: function() {
        return getNextInput(false);
    },
    readObject: function() {
        return getNextInput({});
    },
    check: function (val) {
        return val;
    },
    assert: function (val) {
        return val;
    },
    choose: function (funcs) {
        if (funcs.length > 1) {
            let i;
            for(i = 0; i < funcs.length - 1; i++) {
                if (getNextInput(false)) {
                    break;
                }
            }
            return funcs[i]();
        } else {
            return funcs[0]();
        }
    }
};
