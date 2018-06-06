const { CPSolver } = require("./cp");

class G_Strings extends CPSolver {

  constructor(cmd = null, mzn = null, dzn = null) {
      const c = cmd ? cmd :
            "/home/roberto/G-Strings/gecode-5.0.0/tools/flatzinc/mzn-gstrings";
      const m = mzn ? mzn : "model.mzn";
      const d = dzn ? dzn : "data.dzn" ;
      super(c, m, d);
  }
  
}

module.exports = G_Strings;
