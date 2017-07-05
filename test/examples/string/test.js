/* global J$ */

var x = J$.readInput();

if (/abc*d*e+\w+/.test(x)) {
    console.log("success");
}
