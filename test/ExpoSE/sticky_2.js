/* Copyright (c) Royal Holloway, University of London | Contact Blake Loring (blake@parsed.uk), Duncan Mitchell (Duncan.Mitchell.2015@rhul.ac.uk), or Johannes Kinder (johannes.kinder@rhul.ac.uk) for details or support | LICENSE.md for license details */

var re = /hello/y;
var x = J$.readInput();

J$.check(x.length < 15);

var i = 0;

while (x.match(re)) {
	i++;
}

if (x > 3) {
	throw 'Unreachable';
}

throw 'Reachable';
