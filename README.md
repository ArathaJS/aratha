# Aratha

Aratha is a prototype dynamic symbolic execution tool for JavaScript built on
[Jalangi 2](https://github.com/Samsung/jalangi2). To run it, you require
a working copy of the [G-Strings](https://bitbucket.org/robama/g-strings.git) CP
solver, or one of the SMT solvers [CVC4](http://cvc4.cs.stanford.edu/) or
[Z3](https://github.com/Z3Prover/z3), as well as Node v7 or higher.

## Running the analysis

First, install the dependencies by running
```
$ npm install
```
from this directory. To analyze a script, run
```
$ npm run analyze -- <path to script>
```
from this directory.

### Options

The default solver is CVC4, and the environment variable `CVC4_PATH` must be set
to the path to CVC4 if `cvc4` is not in your `PATH`.

Alternatively, you can set `SOLVER=z3`to use Z3 instead. In this case,
`Z3_PATH` must point to Z3 (or `z3` must be in your `PATH`).

## Tests

The tests are written with [Mocha](https://mochajs.org/). To run them, run
`npm test` from this directory.
