/* global J$ */

var x = J$.readInput();

if (typeof x === "number") {
    x.a = 7;

    if (x.a === 7) {
        console.log("assignment to number succeeded?");
    } else {
        console.log("all is well");
    }
}
