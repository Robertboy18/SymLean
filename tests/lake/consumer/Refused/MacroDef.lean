module

public import CAS.IncludeStr

/-! A macro that expands to `include_str`, for `MacroUse.lean`. The public import passes the check
on to every module that can expand the macro. -/

public section

macro "embedTwo! " path:str : term => `(include_str $path)

end
