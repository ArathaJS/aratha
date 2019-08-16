/* Copyright (c) Royal Holloway, University of London | Contact Blake Loring (blake@parsed.uk), Duncan Mitchell (Duncan.Mitchell.2015@rhul.ac.uk), or Johannes Kinder (johannes.kinder@rhul.ac.uk) for details or support | LICENSE.md for license details */

//Test modeling of looped references to open capture groups (Local captures)
var x = J$.readInput();

if (/^(([a-z])\2)+$/.test(x)) {

	if (x == '11') {
		throw 'Unreachable';
	}

	if (x == 'ab') {
		throw 'Unreachable';
	}

	if (x == 'aa') {
		throw 'Reachable';
	}

	if (x == 'zz') {
		throw 'Reachable';
	}

	throw 'Reachable';
}
