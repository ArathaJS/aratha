/* global J$ */

var x = {a: 1};
var y = J$.readInput();

x[y] = 2;

if (x[y] === 1) {
    console.log("impossible");
}
