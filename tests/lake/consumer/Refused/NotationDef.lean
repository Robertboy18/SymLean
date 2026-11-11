module

public import CAS.IncludeStr

/-! A notation that expands to `include_str`, for `NotationUse.lean`. -/

public section

notation "embedNote! " path => include_str path

end
