/* Copyright (c) Royal Holloway, University of London | Contact Blake Loring (blake@parsed.uk), Duncan Mitchell (Duncan.Mitchell.2015@rhul.ac.uk), or Johannes Kinder (johannes.kinder@rhul.ac.uk) for details or support | LICENSE.md for license details */

var x = J$.readInput();

if (/^[a-zA-Z]?$/.test(x)) {
	if (!/^[a-z]$/.test(x)) {
		throw 'Reachable';
	} else {
		throw 'Reachable';
	}
}

if (/^[a-z]$/.test(x)) {
	throw 'Unreachable';
}
