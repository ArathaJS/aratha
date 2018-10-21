/* global J$ */

if (J$.readNumber() > 1) {
    console.log("> ok");
}

if (J$.readNumber() >= 1) {
    console.log(">= ok");
}

if (J$.readNumber() <= 1) {
    console.log("<= ok");
}

if (J$.readNumber() < 1) {
    console.log("< ok");
}
