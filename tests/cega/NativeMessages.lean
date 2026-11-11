/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/
import CAS

/-!
# Failure reports of native `cega [fast]`

With `cega.nativeCertificates`, a failing `cega [fast]` restores the state after its native attempt
and runs the kernel routes. When those fail too, the report keeps the native attempt's failure
after the kernel's.
-/

/--
The native attempt of `cega [fast]`, before this kernel fallback, failed with:
  Finite native attempt: CEGA finite certificate evaluates to false
-/
#guard_msgs (substring := true, whitespace := lax) in
set_option cega.nativeCertificates true in
example : ∀ i : Fin 2, i.val = 0 := by
  cega [fast]
