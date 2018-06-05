const MZN = '/home/roberto/G-Strings/gecode-5.0.0/tools/flatzinc/mzn-gstrings'

const child_process = require("child_process");

const { CPSolver } = require("./cp");

class G_Strings extends CPSolver {

  constructor() {
      const gst = child_process.spawn(MZN, []);
      super(gst);  
  }

}

module.exports = G_Strings;
