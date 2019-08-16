/* global J$ */

var s = J$.readString();
var re = /(a+)(b|c)(a+)/;
var result = re.exec(s);
if (result) {
    if (result[2] === "b") {
        console.log("1", result);
    } else {
        console.log("2", result);
    }
} else {
    console.log("3 no match");
    console.log(s);
}
