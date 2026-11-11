module

import Macros.Embed
import CAS.IncludeStr

/-- The same macro in a module that loads the check, which refuses it at the use. -/
public def foreignChecked : String := embedForeign! "data.txt"
