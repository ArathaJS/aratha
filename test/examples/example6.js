/* global J$ */

var x = J$.readInput();

if (typeof x !== "object" && x.length === 1) {
    console.log("success:", x);
} else {
    console.log("failure:", x);
}
