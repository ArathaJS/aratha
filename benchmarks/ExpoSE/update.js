/* Copyright (c) Royal Holloway, University of London | Contact Blake Loring (blake@parsed.uk), Duncan Mitchell (Duncan.Mitchell.2015@rhul.ac.uk), or Johannes Kinder (johannes.kinder@rhul.ac.uk) for details or support | LICENSE.md for license details */


var q = J$.readInput();
var qq = J$.readInput();

if (q.length == 5) {
    q[3] = qq;

    if (q[3] != qq) {
        throw 'Unreachable';
    }

    throw 'Reached';
}
