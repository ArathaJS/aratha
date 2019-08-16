/* global J$ */

var x = {a: 1};
delete x[J$.readInput()];

if (!("a" in x)) {
    console.log("success", x);
}
