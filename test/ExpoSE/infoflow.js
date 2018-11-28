/* Copyright (c) Royal Holloway, University of London | Contact Blake Loring (blake@parsed.uk), Duncan Mitchell (Duncan.Mitchell.2015@rhul.ac.uk), or Johannes Kinder (johannes.kinder@rhul.ac.uk) for details or support | LICENSE.md for license details */

"use strict";


function flowTest(lo, hi) {

    console.log("Inputs: Hi:", hi, "Lo:", lo);

    var result = lo * 42;

    if (lo > 4) {
        console.log("Branch A-then");
        result -= lo;
    } else {
        console.log("Branch A-else");
        if (hi == 777) {
            result = -result;
        }
    }

    if (hi > 0) {
        console.log("Branch B-then");
    } else {
        console.log("Branch B-else");
    }

    console.log("Low output:", result);

    return result;
}

function verify(f) {

    var loInput = J$.readInput();
    var hiInput1 = J$.readInput();
    var hiInput2 = J$.readInput();

    var loOutput1 = f(loInput, hiInput1);
    var loOutput2 = f(loInput, hiInput2);

    if (hiInput1 !== 777 && hiInput2 !== 777) {
    }
}

verify(flowTest);
