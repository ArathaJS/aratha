/* Copyright (c) Royal Holloway, University of London | Contact Blake Loring (blake@parsed.uk), Duncan Mitchell (Duncan.Mitchell.2015@rhul.ac.uk), or Johannes Kinder (johannes.kinder@rhul.ac.uk) for details or support | LICENSE.md for license details */

var x = J$.readInput();
var b = /abc/g.exec(x);

J$.check(x.length < 4);

if (b.exec(x)) {
	
	if (b.exec(x)) {
		//As string length is < 4 two abc is unreachable
		throw 'Unreachable';
	}

	//One abc is reachable
	throw 'Reachable';
}

throw 'Reachable';
