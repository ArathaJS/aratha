/* global J$ */

var x = J$.readInput();

if (typeof x === "string") {
    console.log("success; x: ", x);
} else {
    console.log("failure: x: ", x);
}
