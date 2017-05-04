/* global J$ */

var x = {a: 1};

x[J$.readInput()] = 4;

if (x.a === 4) {
    console.log("success");
}
