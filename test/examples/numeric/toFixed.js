/* global J$ */

var x = J$.readNumber();
var n = J$.readNumber();

if (x.toFixed(n) === "5") {
    console.log("success")
    console.log("x = ", x);
    console.log("n = ", n);
}
