# Concolic analysis for Jalangi 2

This is a prototype concolic analysis tool for Jalangi 2. To run it, you require
a working copy of either the [CVC4](http://cvc4.cs.stanford.edu/) or the
[Z3](https://github.com/Z3Prover/z3) SMT solver and Node.js v7 or up, as well as
a working setup of Jalangi 2.

## How to run the analysis

The default solver is CVC4, and the environment variable `CVC4_PATH` must be set
to the path to CVC4, if it is not in your `PATH`.

Alternatively, you can set `SMT_SOLVER=z3`to use Z3 instead. In this case,
`Z3_PATH` must point to Z3 (or `z3` must be in your `PATH`).

To analyze a script, run

```
node ../src/js/commands/jalangi.js --analysis ./ <path to script>
```

from this directory.
