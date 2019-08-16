/* global J$ */

var x = J$.readInput();

if (x.a === 3) {
    console.log("three");
}

x.a = 5;
var y = J$.readInput();

if (typeof x === "object" && y === "a") {
    if (x[y] === 5) {
        console.log("five");
    } else {
        throw new Error("failed to modify object");
    }
}
