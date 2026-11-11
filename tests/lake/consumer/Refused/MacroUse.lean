module

import Refused.MacroDef

/-- The macro of `Refused.MacroDef`, refused at this use by the check that it passes on. -/
public def macroTwo : String := embedTwo! "data.txt"
