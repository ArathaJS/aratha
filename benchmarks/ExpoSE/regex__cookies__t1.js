var S$ = require('S$');

function loadSrc(obj, src) {
    throw src;
}

var cookies = S$.symbol('Cookie');
var world = {};

if (cookies) {
    if (/iPhone/.exec(cookies)) {
        loadSrc(world, '/resources/' + cookies);
    }

    loadSrc(world, '/resources/unknown');
} else {
    loadSrc(world, '/resources/fresh');
}
