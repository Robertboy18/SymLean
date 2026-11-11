/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/
module

public import CAS.IncludeStr

/-!
# A data file of the library

The path of `include_str` is on the next line, which the build of the library must track.
-/

/-- The text of `data.txt`, which `run.sh` writes. -/
public def casData : String := include_str
  "data.txt"
