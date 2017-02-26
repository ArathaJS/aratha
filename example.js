function foo() {
    console.log("foo");
}

function bar() {
    console.log("bar");
}

function program(b) {
    for (var i = 0; i < 10 && b === b; ++i) {
        if (i % 2 === 0) {
            foo();
        } else {
            bar();
        }
    }
    console.log("done");
}

program(J$.readInput());
