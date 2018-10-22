const { CPSolver } = require("./cp");

class G_Strings extends CPSolver {

  constructor(options, mzn = null, mzn2fzn = null, fzn = null) {
      super(options);
      const path = "/home/roberto/G-Strings/gecode-5.0.0/tools/flatzinc/";
      this._mzn = mzn ? mzn : path + "mzn-gstrings";
      this._mzn2fzn = mzn2fzn ? mzn2fzn : path + "mzn2fzn-gstrings";
      this._fzn = fzn ? fzn : path + "fzn-gstrings";
  }
      
  mzn2fzn() {
      return this._mzn2fzn;   
  }
  
  mzn() {
      return this._mzn;   
  }
  
  fzn() {
      return this._fzn;   
  }
  
}

module.exports = G_Strings;
