module

import Macros.Embed

/-- The macro of another library, which reads a file here: the facet refuses this module, which
does not load the check. -/
public def foreignUse : String := embedForeign! "data.txt"
