/* Copyright (c) Royal Holloway, University of London | Contact Blake Loring (blake@parsed.uk), Duncan Mitchell (Duncan.Mitchell.2015@rhul.ac.uk), or Johannes Kinder (johannes.kinder@rhul.ac.uk) for details or support | LICENSE.md for license details */


var x = J$.readInput();
var y = J$.readInput();

if (x == 0 && y == false) {} //Force x to false at least once

if (!(x == y)) {
	console.log('Here');
	throw 'Boo';
}
