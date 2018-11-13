/* global J$ */

var n = J$.readNumber();

if (n < 3 && Math.abs(n) > 3) {
    console.log("success");
    console.log("n = ", n);
}
