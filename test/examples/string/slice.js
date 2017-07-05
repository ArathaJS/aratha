/* global J$ */

var x = J$.readInput();

if (x.slice(-4) === "test") {
    console.log(1);
}

if (x.slice(2, -12) === "abcdef") {
    console.log(2);
}
