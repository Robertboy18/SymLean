/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS
public meta import CAS
public import HexBareissTheory
public meta import HexBareissTheory

/-!
# Determinants through Hex: `#cas [det]`

With Hex (the optional build `lake -R -Khex=on build CASHex`), `#cas [det] A` evaluates the
determinant of a square matrix literal with rational entries by Hex's simproc `Hex.norm_det`
instead of Mathlib's `norm_det`, and reports `A.det = d` with the proof the simproc builds.
`detBackend` registers `logDet` as the backend of the `#cas` mode `det` with `@[cas_route det]`
(`CAS.Tactic.RouteRegistry`).

## Implementation notes

`logDet` writes `A` as a Mathlib matrix over `ℚ` and runs `Simp.main` with `Hex.norm_det` as its
only simproc, so the proof of `A.det = d` is Hex's certificate. Hex's fraction-free (Bareiss)
elimination runs in compiled code and proposes it: the row swaps, a lower triangular transform
`L` with `L * σA` upper triangular, and the value, or a left kernel vector when the matrix is
singular, after scaling each row of a rational matrix to integers. The kernel checks the
certificate by evaluation (`HexMatrixTheory.det_eq_of_checkRat'`) instead of replaying the
elimination; Hex puts the cost at about `n³ / 3` products of integers the size of the minors.
We then check `A.det = d` once more in the kernel, as an auxiliary theorem (`evidence`), before
printing it. Without Hex, `#cas [det]` proves the value with Mathlib's `norm_det`.

## References

* The Lean FRO and the Hex contributors, *hex: Verified computational algebra in Lean 4*,
  release v0.10.0, 2026, <https://github.com/leanprover/hex/tree/v0.10.0>.
  We call its simproc `Hex.norm_det` (HexBareissTheory).
* Erwin H. Bareiss, "Sylvester's Identity and Multistep Integer-Preserving Gaussian Elimination",
  *Mathematics of Computation* 22 (1968), pp. 565-578,
  <https://doi.org/10.1090/S0025-5718-1968-0226829-0>.
  The one-step integer-preserving elimination of Section I, Eq. (8), whose last pivot is the
  determinant, is the fraction-free elimination of Hex's certificate search.
-/

public meta section

namespace CASHex.LinearAlgebra

open Lean Elab Command Meta Term
open CAS.Command CAS.Command.InfoView
open CAS.Command.LinearAlgebra

/-- Run `#cas [det] A` through Hex. -/
def logDet (ref input : Syntax) : CommandElabM Unit := do
  let A ← parseQMatrix input
  unless A.rows = A.cols do throwErrorAt input "det: the matrix must be square"
  let (proposition, proof, d) : Lean.Expr × Lean.Expr × ℚ ← liftTermElabM do
    let At ← matrixTerm A A.rows A.cols
    let e ← elabTerm (← `(Matrix.det $At)) none
    synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let simprocs ← ({} : Simp.Simprocs).add `Hex.norm_det (post := true)
    let (result, _) ← Simp.main e (← Simp.mkContext {})
      (methods := Simp.mkDefaultMethodsCore #[simprocs])
    let some d ← CAS.Tactic.Classify.rationalLiteral? result.expr
      | throwError "det: Hex's norm_det did not reduce the determinant to a number"
    let proof ← match result.proof? with
      | some proof => pure proof
      | none => mkEqRefl e
    return (← mkEq e result.expr, proof, d)
  logReport ref {
    domain := matrixDomain A
    input := A.text
    inputType := "matrix"
    output := CAS.Command.Algebra.ratText d
    outputType := "determinant (Hex's Bareiss certificate)"
  } #[← evidence "det" "Determinant" proposition proof]

/-- `#cas [det] A` through Hex, as the backend of the `#cas` mode `det`. -/
@[cas_route det]
def detBackend : CAS.Tactic.RouteRegistry.CommandBackend := fun stx ↦ do
  let `(#cas [det] $A:term) := stx | return false
  logDet A A
  return true

end CASHex.LinearAlgebra
