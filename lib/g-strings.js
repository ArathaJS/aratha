const { CPSolver } = require("./cp");

class G_Strings extends CPSolver {

  constructor(options, mzn = "", mzn2fzn = "", fzn = "") {
      super(options);
      this._mzn = mzn + "mzn-gstrings";
      this._mzn2fzn = mzn2fzn + "mzn2fzn-gstrings";
      this._fzn = fzn + "fzn-gstrings";
      this.id = "G-Strings";
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
