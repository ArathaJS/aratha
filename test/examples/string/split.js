/* global J$ */

var x = J$.readString();
var y = x.split(":");

if (y[0] === "foo" && y[1] === "bar") {
    console.log("success: x = ", x);
} else {
    console.log("failure");
}
