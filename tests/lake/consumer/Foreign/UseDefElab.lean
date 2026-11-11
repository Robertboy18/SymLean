module

import Macros.EmbedDefElab

/-! The command elaborator of another library, whose expansion reads a file here: the facet
refuses this module, which does not load the check. -/

embedDefElabForeign foreignDefElab "data.txt"
