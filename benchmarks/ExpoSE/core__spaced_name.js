var S$ = require('S$');

var x = S$.symbol('X');

if (x) {
	throw 'Reachable';
}
