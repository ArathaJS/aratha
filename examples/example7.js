/* global J$ */

var x = J$.readInput();

if (x.a === 3) {
    console.log("three");
}

x.a = 5;

if (typeof x === "object") {
    if (x.a === 5) {
        console.log("five");
    } else {
        throw new Error("failed to modify object");
    }
}
