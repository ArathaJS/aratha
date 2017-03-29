# Concolic analysis for Jalangi 2

This is a prototype concolic analysis tool for Jalangi 2. To run it, you require
a working copy of the [Z3](https://github.com/Z3Prover/z3) SMT solver and
Node.js v7 or up, as well as a working setup of Jalangi 2.

## How to run the analysis

The environment variable `SMT_SOLVER` must be set to the path to Z3. To analyze
a script, run

```
node ../src/js/commands/jalangi.js --inlineIID --inlineSource --analysis ./ <path to script>
```

from this directory.
