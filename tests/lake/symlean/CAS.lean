/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/
module

public import CAS.Embedded

/-!
# A stand-in for the library

`run.sh` builds this package with SymLean's configuration and SymLean's `CAS/IncludeStr.lean` in
place of the library, as the root package and as a dependency, so that the runs neither rebuild
the library nor change the options that Lake caches with the repository's configuration.
-/
