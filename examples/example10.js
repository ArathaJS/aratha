/* global J$ */

// NOTE: this test does not work in Z3 4.5.0 due to a bug.
// See https://github.com/Z3Prover/z3/issues/957 for more information.
var x = {a: 1};
var y = J$.readInput();

if (x[y] === 1) {
    console.log("success");
}
