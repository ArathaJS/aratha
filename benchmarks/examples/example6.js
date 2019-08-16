/* global J$ */

var x = J$.readInput();

if (typeof x !== "object" && typeof x !== "function" && x.length === 1) {
    console.log("success:", x);
} else {
    console.log("failure:", x);
}
