module

import Macros.Direct

/-- A module that loads a declaration's own embedded file, which Lean read in `Macros.Direct`:
this needs no check here. -/
public def foreignPlain : String := direct
