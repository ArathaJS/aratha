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

The default solver is G-Strings. Once the solver is installed, you need to 
modify the `path` variable in G_Strings class (in `lib/g-strings.js`) with the 
proper path to `<GDIR>/G-Strings/gecode-5.0.0/tools/flatzinc/`, where `<GDIR>`
is the folder where G-Strings is installed.

Alternatively, you can use an SMT solver by setting `SOLVER=cvc4` or `SOLVER=z3`
to use CVC4 or Z3 solver respectively. Note that the environment variable
`CVC4_PATH` (resp., `Z3_PATH`) must be set to the path to CVC4 (resp., Z3) if
`cvc4` (resp., `z3`) is not in your `PATH`.

## Tests

The tests are written with [Mocha](https://mochajs.org/). To run them, run
`npm test` from this directory.
