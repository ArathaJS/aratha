/* Copyright (c) Royal Holloway, University of London | Contact Blake Loring (blake@parsed.uk), Duncan Mitchell (Duncan.Mitchell.2015@rhul.ac.uk), or Johannes Kinder (johannes.kinder@rhul.ac.uk) for details or support | LICENSE.md for license details */


var x = {
    a: 'hi',
    b: 'bob',
    c: 'john'
}

var a = x[J$.readInput()];

if (a && a == 'john') {
    console.log('I SHOULD BE REACHABLE!!')
    throw 'Reachable';
}
