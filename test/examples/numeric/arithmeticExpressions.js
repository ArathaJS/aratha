/* global J$ */

var x = J$.readInput(), y = J$.readInput(), z = J$.readInput();

if (x / 2 - y === 3) {
    console.log("one: x=" + x + " y=" + y);
}

if (z % 12 === x) {
    console.log("two: x=" + x + " y=" + y + " z=" + z);
}
