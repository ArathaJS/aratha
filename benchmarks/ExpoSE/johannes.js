/* Copyright (c) Royal Holloway, University of London | Contact Blake Loring (blake@parsed.uk), Duncan Mitchell (Duncan.Mitchell.2015@rhul.ac.uk), or Johannes Kinder (johannes.kinder@rhul.ac.uk) for details or support | LICENSE.md for license details */

"use strict";


function f(x, maxLen) {
    var s = x.match(/<([a-z]+)>(.*?)<\/\1>/);
    if (s) {
        if (s[2].length <= 0) {
            throw '*** Element Missing ***';
        } else if (s[2].length > maxLen) {
            throw '*** Element Too Long ***';
        } else {
            throw '*** Success ***';
        }
    } else {
        throw '*** Malformed XML ***';
    }
}

var len = J$.readInput();
var str = J$.readInput();

J$.check(str.length < 10);

f(str, len);
