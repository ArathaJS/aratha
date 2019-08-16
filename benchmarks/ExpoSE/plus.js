/* Copyright (c) Royal Holloway, University of London | Contact Blake Loring (blake@parsed.uk), Duncan Mitchell (Duncan.Mitchell.2015@rhul.ac.uk), or Johannes Kinder (johannes.kinder@rhul.ac.uk) for details or support | LICENSE.md for license details */

//Test the + operator

var x = J$.readInput();

if (/^(hello)+(world)+$/.test(x)) {

	if (x.length == 0) {
		throw 'Unreachable';
	}

	if (x == '') {
		throw 'Unreachable';
	}

	if (x == 'hellohelloworld') {
		throw 'Reachable';
	}

	throw 'Reachable';
}

if (/^he+l+l+o_wor+l+d+$/.test(x)) {
	
	if (x == 'helllllo_world') {
		throw 'Reachable';
	}

	if (x == 'hello_world') {
		throw 'Reachable';
	}

	if (x == 'hellooooo_world') {
		throw 'Unreachable';
	}

	if (x.length == 0) {
		throw 'Unreachable';
	}

	throw 'Reachable';
}

if (/^h+$/.test(x)) {

	if (/^[^h]+$/.test(x)) {
		throw 'Unreachable';
	}

	throw 'Reachable';
}

if (/^z+$/.test(x)) {
	J$.check(x.length < 5);
	
	for (var i = 0; i < x.length; i++) {
		if (x[i] != 'z') {
			throw 'Unreachable';
		}
	}

	throw 'Reachable';
}

throw 'Reachable';
