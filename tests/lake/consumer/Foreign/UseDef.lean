module

import Macros.EmbedDef

/-! The command macro of another library, whose expansion reads a file here: the facet refuses
this module, which does not load the check. -/

embedDefForeign foreignDef "data.txt"
