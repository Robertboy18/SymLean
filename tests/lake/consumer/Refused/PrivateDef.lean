module

import CAS.IncludeStr

/-! A macro that expands to `include_str` in a module that imports the check privately, so that a
module that expands the macro would not load the check: the facet refuses this module. -/

public section

macro "embedPrivate! " path:str : term => `(include_str $path)

end
