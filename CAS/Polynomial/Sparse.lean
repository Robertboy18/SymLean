/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Polynomial.Sparse.UnivariateCalculus

/-!
# Checked sparse polynomial identities

The executable zero check `isZero` used by sparse-polynomial certificates and the identity check
`identityHolds`, with their real-valued meaning for one variable (`evalReal_eq_zero_of_isZero`,
`evalReal_eq_of_isZero_sub`). They rest on the three modules of the foundational
sparse-polynomial API, all imported:

* `Sparse.Representation` defines ordered monomials, canonical sparse
  arithmetic, and polynomial reflection;
* `Sparse.Semantics` proves real-evaluation soundness and reification
  correctness;
* `Sparse.UnivariateCalculus` provides one-variable evaluation and the analytic
  derivative bridge.

The sparse carrier `Alg.MvPoly` has exponent vectors as monomials. It is distinct from the
carrier `Alg.Poly` of `CAS.ClosedForm.Expression.Polynomial.Normalization`, which rewrites
`Verified.Expr` syntax and whose monomials are lists of opaque factors. Code that moves between
the two uses the proved bridges: `mvPolyOf?` and `mvPolyExpr` for polynomials in the
coordinates `Fin n`, and `Canonical.compile` and `Canonical.render` (`eval_compile`,
`eval_render`) for rational expressions over a sorted table of atoms.
-/

@[expose] public section

namespace CAS.Polynomial.Sparse

/-- Decide whether a sparse polynomial is zero after canonicalization. -/
def isZero {n : Nat} (polynomial : Verified.Expr.Alg.MvPoly n) : Bool :=
  (Verified.Expr.Alg.mvNormalize polynomial).isEmpty

/-- A polynomial accepted as sparse zero evaluates to zero everywhere. -/
theorem evalReal_eq_zero_of_isZero {polynomial : Univariate}
    (hzero : isZero polynomial = true) (x : ℝ) :
    evalReal polynomial x = 0 := by
  rw [← evalReal_normalize polynomial x, List.isEmpty_iff.mp hzero]
  rfl

/-- Decide whether the sparse polynomials `left` and `right` are equal by checking that their
difference normalizes to zero. -/
def identityHolds (left right : Univariate) : Bool :=
  isZero (Verified.Expr.Alg.mvSub left right)

/-- A checked sparse zero difference proves pointwise real equality. -/
theorem evalReal_eq_of_isZero_sub {left right : Univariate}
    (hzero : isZero (Verified.Expr.Alg.mvSub left right) = true)
    (x : ℝ) :
    evalReal left x = evalReal right x :=
  sub_eq_zero.mp ((evalReal_sub left right x).symm.trans (evalReal_eq_zero_of_isZero hzero x))

end CAS.Polynomial.Sparse
