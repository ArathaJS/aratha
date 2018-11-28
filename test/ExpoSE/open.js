/* Copyright (c) Royal Holloway, University of London | Contact Blake Loring (blake@parsed.uk), Duncan Mitchell (Duncan.Mitchell.2015@rhul.ac.uk), or Johannes Kinder (johannes.kinder@rhul.ac.uk) for details or support | LICENSE.md for license details */

//Test modeling of looped references to open capture groups (Local captures)
var x = J$.readInput();

if (/^((.)\2)+$/.test(x)) {

	if (x == 'aa') {
		throw 'Reachable';
	}

	if (x == 'bb') {
		throw 'Reachable';
	}

	if (x == 'cc') {
		throw 'Reachable';
	}

	throw 'Reachable';
}
