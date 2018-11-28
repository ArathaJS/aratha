/* Copyright (c) Royal Holloway, University of London | Contact Blake Loring (blake@parsed.uk), Duncan Mitchell (Duncan.Mitchell.2015@rhul.ac.uk), or Johannes Kinder (johannes.kinder@rhul.ac.uk) for details or support | LICENSE.md for license details */

"use strict";

var x = J$.readInput();

if (x.length > 0 && x !== 'hello' && x.replace('h...o', '') === '') {
	console.log('A length: ' + x.length);
}
