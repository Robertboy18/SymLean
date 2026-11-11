module

/-! A macro that expands to `include_str`, in a library that does not list the facet, so that
nothing here loads the check. -/

public section

macro "embedForeign! " path:str : term => `(include_str $path)

end
