/* global J$ */

var str = J$.readString();
var num = J$.readNumber();

var x = parseInt(str, 10);

if (x === num) {
    console.log("parseInt(", str, ", 10) ===", num);
} else if (x !== num) {
    console.log("parseInt(", str, ", 10) !==", num);
} else {
    console.log("impossible");
}
