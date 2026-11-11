/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS
public meta import CAS.CEGA

/-!
# The `cega` tactic on integrals with a nonsmooth point

Where the domain checker certifies no fourth derivative, bare `cega` bounds the integral by
range panels, which only need continuity: the square root at the endpoint zero and the absolute
value at the corner.
-/

@[expose] public section

namespace CAS.Examples.CEGA.NonsmoothIntegrals

open CAS.Certificate
open CAS.CEGA

/-- The square root is continuous at zero, although its derivative is singular there. -/
example : (∫ x in (0 : ℝ)..1, Real.sqrt x) < 1 := by
  cega

/-- Continuity also suffices for a bound across the corner of the absolute value. -/
example : (∫ x in (-1 : ℝ)..1, |x|) < 2 := by
  cega

end CAS.Examples.CEGA.NonsmoothIntegrals
