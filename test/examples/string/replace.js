/* global J$ */

var x = J$.readInput();

if (x.replace("abc", "def") === "blabladef") {
    console.log(1);
}

var y = J$.readInput();

if ("test123".replace(y, "234") === "test1234") {
    console.log(2);
}

var z = J$.readInput();

if ("test123".replace("123", z) === "testpineapple") {
    console.log(3);
}
