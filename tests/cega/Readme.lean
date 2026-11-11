/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/
import CAS

/-!
# The fast-profile example of the README

`README.md` (section "Fast certificates") proves `fast_rows` with `cega [fast]` under
`cega.nativeCertificates` and prints its axioms: the theorem shows the native certificate among
them. That axiom would enter the library, so the example is pinned here, outside `lake build`. The
suffix of the axiom's name depends on the elaboration mode (`ax_1_1` with `Elab.async`, the
default, and `ax_1` without), so only its common prefix is pinned.
-/

set_option cega.nativeCertificates true in
theorem fast_rows : ∀ i : Fin 64, (i.val : ℤ) ^ 2 < 4096 := by
  cega [fast]

/-- info: 'fast_rows' depends on axioms: [propext, fast_rows._native.cegaFast.ax_1 -/
#guard_msgs (substring := true) in
#print axioms fast_rows
