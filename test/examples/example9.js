/* global J$ */

var x = J$.readInput();

if (x.a === 1) {
    throw new Error("fail");
}

x.a = 1;
x.b = 2;

if (x.a === 1) {
    console.log("success", x);
}
