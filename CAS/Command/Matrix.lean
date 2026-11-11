/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Analysis.Matrix.PosDefCertificate
public import CAS.Command.Digits
public import CAS.Command.LinearAlgebra.Basic

/-!
# Positive definiteness and Rayleigh bounds: `#cas [positiveDefinite]`, `#cas [eigenvalueBounds]`

`#cas [positiveDefinite] !![a, b; c, d]` decides whether a matrix with rational entries is positive
definite, as Mathematica's `PositiveDefiniteMatrixQ` does, and proves the answer: either
`(!![…] : Matrix (Fin n) (Fin n) ℝ).PosDef`, or its negation with an explicit rational vector
`x ≠ 0` and `xᵀ A x ≤ 0`, or its negation because the matrix is not symmetric.

`#cas [eigenvalueBounds] !![…]` takes a symmetric matrix and prints decimals `c` and `μ` with six
places (`#cas (digits := d) [eigenvalueBounds]` sets the number `d` of places) such that
`c ∑ xᵢ² ≤ ∑ᵢ ∑ⱼ A i j xᵢ xⱼ ≤ μ ∑ xᵢ²` for every real vector `x`, while rational vectors `x` and
`y` have `xᵀ A x < (c + 10 ^ (-d)) ∑ xᵢ²` and `yᵀ A y > (μ - 10 ^ (-d)) ∑ yᵢ²`. So `c` is the
smallest eigenvalue rounded down to `d` places and `μ` the largest one rounded up.

## Implementation notes

The search is the exact symmetric elimination `A = L D Lᵀ` over `ℚ` (`QMatrix.ldl` of
`CAS/Command/LinearAlgebra/Basic.lean`), which either factors the matrix or returns a rational
vector whose quadratic form shows that it is not positive definite. The kernel checks the
factorization entry by entry and the signs of the pivots (`posDef_of_ldlCheck`), or the quadratic
form of the vector (`not_posDef_of_quadFormCheck`). An asymmetric matrix is refuted by `norm_num`
at one entry (`Matrix.conjTranspose_apply`). These theorems and those of the bounds are in
`CAS/Analysis/Matrix/PosDefCertificate.lean`, and `certify` applies them to a hypothesis that the
kernel decides.

Both bounds come from bisection on the grid `10 ^ (-d) ℤ` (`lowerGridPoint`), where each step
decides by exact elimination whether `A - t I` is positive semidefinite: it either factors with
nonnegative pivots or yields a vector with a negative quadratic form. The row-sum bound
`rowSumBound` only brackets the start of the bisection, and no proof uses it; the largest
eigenvalue is minus the smallest one of `-A`. The kernel checks the factorizations of `A - c I`
and `μ I - A` (`quadForm_ge_of_ldlCheck`, `quadForm_le_of_ldlCheck`) and the two vectors
(`exists_quadForm_lt`, `exists_quadForm_gt`).
-/

public meta section

namespace CAS.Command.Matrix

open Lean Elab Command Meta Term
open CAS.Command.InfoView CAS.Command.LinearAlgebra
open CAS.Command.Algebra (natTerm proveStatement)

/-- Elaborate a closed term. -/
def elabClosed (stx : TSyntax `term) : TermElabM Lean.Expr := do
  let e ← elabTerm stx none
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

/-- The rows of `A` as the function `(![![a, …], …] : Fin m → Fin n → ℚ)`. -/
def rowsTerm (A : QMatrix) : TermElabM (TSyntax `term) := do
  let rows ← A.mapM fun row ↦ do `(![$(← row.mapM ratTerm),*])
  `((![$rows,*] : Fin $(natTerm A.rows) → Fin $(natTerm A.cols) → ℚ))

/-- The entries of a square matrix below the diagonal, with zeros elsewhere. -/
def strictLower (L : QMatrix) : QMatrix :=
  L.mapIdx fun i row ↦ row.mapIdx fun j a ↦ if j < i then a else 0

/-- `z / 10 ^ d` for `d ≥ 1` as a decimal literal of the field `K`, such as `(1.267949 : ℝ)`. -/
def decimalTerm (K : TSyntax `term) (z : Int) (d : Nat) : TermElabM (TSyntax `term) := do
  if z = 0 then return ← `((0 : $K))
  let literal : TSyntax `term := ⟨(Syntax.mkScientificLit (Digits.renderDecimal z.natAbs d)).raw⟩
  if z < 0 then `((-$literal : $K)) else `(($literal : $K))

/-- The theorem `thm` applied to `args` and to a proof of its next hypothesis, a decidable
proposition about rational numbers that the kernel checks by evaluation. -/
def certify (operation : String) (thm : Name) (args : Array Lean.Expr) : TermElabM Lean.Expr := do
  let partialProof ← mkAppOptM thm (#[none] ++ args.map some)
  let .forallE _ check _ _ ← whnfR (← inferType partialProof)
    | throwError "{operation}: unexpected shape of the theorem {thm}"
  return mkApp partialProof (← CAS.Tactic.KernelReadBack.decideByKernel operation check)

/-- The term `show M = Matrix.of fun i j ↦ ((Aq i j : ℚ) : ℝ) from …` for the real matrix literal
`M` of `A` and the elaborated rows `Aq` of `A`, to rewrite a statement about `M` into the form of
the certificate theorems. -/
def ofRows (A : QMatrix) (M : TSyntax `term) (Aq : Lean.Expr) : TermElabM (TSyntax `term) := do
  let rows ← exprToSyntax Aq
  let castRows ← A.mapM fun row ↦ do
    `(![$(← row.mapM fun a ↦ do `((($(← ratSyntax a) : ℚ) : ℝ))),*])
  let cast ← `((![$castRows,*] : Fin $(natTerm A.rows) → Fin $(natTerm A.cols) → ℝ))
  `(show $M = Matrix.of (fun i j ↦ (($rows i j : ℚ) : ℝ)) from by
      rw [show (fun i j ↦ (($rows i j : ℚ) : ℝ)) =
          FinVec.map (fun r ↦ FinVec.map (Rat.cast : ℚ → ℝ) r) $rows from by
        simp only [FinVec.map_eq]; rfl]
      change _ = Matrix.of $cast
      norm_num)

/-- The largest integer `m` such that `A - (m / 10 ^ d) I` is positive semidefinite, for a
symmetric matrix `A`, with the factorization `(L, D)` of `A - (m / 10 ^ d) I` and a rational
vector `x` with `xᵀ (A - ((m + 1) / 10 ^ d) I) x < 0`. Bisection between `-K` and `K + 1` for
`K = ⌈R 10 ^ d⌉`, where the row-sum bound `R` bounds the absolute value of every eigenvalue; each
step decides semidefiniteness by `QMatrix.ldl`. -/
def lowerGridPoint (A : QMatrix) (d : Nat) : Option (Int × (QMatrix × Array ℚ) × Array ℚ) :=
  Id.run do
  let scale : ℚ := 10 ^ d
  let semidefinite (m : Int) := (A.subScalar ((m : ℚ) / scale)).ldl false
  let K : Int := ⌈A.rowSumBound * scale⌉
  let mut lo := -K
  let mut hi := K + 1
  while hi - lo > 1 do
    let m := (lo + hi) / 2
    if (semidefinite m).toBool then lo := m else hi := m
  match semidefinite lo, semidefinite hi with
  | .ok factor, .error x => return some (lo, factor, x)
  | _, _ => return none

/-- Run `#cas [positiveDefinite] A`. -/
def logPosDef (ref : Syntax) (input : Syntax) : CommandElabM Unit := do
  let A ← parseQMatrix input
  unless A.rows = A.cols do throwErrorAt input "positiveDefinite: the matrix must be square"
  let n := A.rows
  let report (output label : String) (certificate : Array MessageData)
      (proposition proof : Lean.Expr) : CommandElabM Unit := do
    let checked ← evidence "positiveDefinite" label proposition proof
    logReport ref {
      domain := s!"{n} × {n} real matrix", input := surfaceText input
      inputType := "matrix", output, outputType := "Boolean" }
      (if certificate.isEmpty then #[checked]
       else #[computationNode "Certificate" certificate, checked])
  if let some (i, j) := A.asymmetricEntry? then
    let (proposition, proof) ← liftTermElabM do
      let M ← matrixTermOver A (← `(ℝ))
      proveStatement "positiveDefinite" (← `(¬ ($M).PosDef)) (← `(tactic| exact fun h ↦ by
        have h' := congrFun (congrFun h.1 ($(natTerm i) : Fin $(natTerm n)))
          ($(natTerm j) : Fin $(natTerm n))
        norm_num [Matrix.conjTranspose_apply] at h'))
    report "False (not symmetric)" "The matrix is not Hermitian" #[] proposition proof
    return
  match A.ldl true with
  | .error x =>
      let (proposition, proof) ← liftTermElabM do
        let M ← matrixTermOver A (← `(ℝ))
        let Aq ← elabClosed (← rowsTerm A)
        let certificate ← certify "positiveDefinite"
          ``CAS.Analysis.Matrix.not_posDef_of_quadFormCheck #[Aq, ← elabClosed (← vectorTerm x)]
        proveStatement "positiveDefinite" (← `(¬ ($M).PosDef)) (← `(tactic| (
          rw [$(← ofRows A M Aq):term]
          exact $(← exprToSyntax certificate))))
      report s!"False (xᵀAx ≤ 0 for x = {x.toList})" "A vector with a nonpositive quadratic form"
        #[] proposition proof
  | .ok (L, D) =>
      let (proposition, proof) ← liftTermElabM do
        let M ← matrixTermOver A (← `(ℝ))
        let Aq ← elabClosed (← rowsTerm A)
        let certificate ← certify "positiveDefinite" ``CAS.Analysis.Matrix.posDef_of_ldlCheck
          #[Aq, ← elabClosed (← rowsTerm (strictLower L)), ← elabClosed (← vectorTerm D)]
        proveStatement "positiveDefinite" (← `(($M).PosDef)) (← `(tactic| (
          rw [$(← ofRows A M Aq):term]
          exact $(← exprToSyntax certificate))))
      report "True" "The matrix is positive definite"
        #[m!"A = L D Lᵀ over ℚ with pivots D = {toString D.toList}, all positive"] proposition proof

/-- Run `#cas [eigenvalueBounds] A`. -/
def logEigenBounds (ref : Syntax) (digits : Nat) (input : Syntax) : CommandElabM Unit := do
  let A ← parseQMatrix input
  unless A.rows = A.cols do throwErrorAt input "eigenvalueBounds: the matrix must be square"
  if A.asymmetricEntry?.isSome then
    throwErrorAt input "eigenvalueBounds needs a symmetric matrix"
  let n := A.rows
  let some (lo, (L, D), x) := lowerGridPoint A digits
    | throwErrorAt input "eigenvalueBounds: the bisection for the smallest eigenvalue failed"
  let some (lo', (L', D'), y) := lowerGridPoint (A.map (·.map (- ·))) digits
    | throwErrorAt input "eigenvalueBounds: the bisection for the largest eigenvalue failed"
  -- `c = lo / 10 ^ d` and `μ = -lo' / 10 ^ d`; `-A - (lo' / 10 ^ d) I = μ I - A`.
  let (proposition, proof) ← liftTermElabM do
    let real ← `(ℝ)
    let rational ← `(ℚ)
    let decimal (z : Int) : TermElabM Lean.Expr := do elabClosed (← decimalTerm rational z digits)
    let M ← matrixTermOver A real
    let Aq ← elabClosed (← rowsTerm A)
    let lower ← certify "eigenvalueBounds" ``CAS.Analysis.Matrix.quadForm_ge_of_ldlCheck
      #[Aq, ← elabClosed (← rowsTerm (strictLower L)), ← elabClosed (← vectorTerm D),
        ← decimal lo]
    let upper ← certify "eigenvalueBounds" ``CAS.Analysis.Matrix.quadForm_le_of_ldlCheck
      #[Aq, ← elabClosed (← rowsTerm (strictLower L')), ← elabClosed (← vectorTerm D'),
        ← decimal (-lo')]
    let below ← certify "eigenvalueBounds" ``CAS.Analysis.Matrix.exists_quadForm_lt
      #[Aq, ← decimal (lo + 1), ← elabClosed (← vectorTerm x)]
    let above ← certify "eigenvalueBounds" ``CAS.Analysis.Matrix.exists_quadForm_gt
      #[Aq, ← decimal (-lo' - 1), ← elabClosed (← vectorTerm y)]
    let c ← decimalTerm real lo digits
    let μ ← decimalTerm real (-lo') digits
    let c' ← decimalTerm real (lo + 1) digits
    let μ' ← decimalTerm real (-lo' - 1) digits
    let size := natTerm n
    let statement ← `((∀ x : Fin $size → ℝ, $c * ∑ i, x i ^ 2 ≤ ∑ i, ∑ j, $M i j * x i * x j ∧
        ∑ i, ∑ j, $M i j * x i * x j ≤ $μ * ∑ i, x i ^ 2) ∧
      (∃ x : Fin $size → ℝ, ∑ i, ∑ j, $M i j * x i * x j < $c' * ∑ i, x i ^ 2) ∧
      (∃ x : Fin $size → ℝ, $μ' * ∑ i, x i ^ 2 < ∑ i, ∑ j, $M i j * x i * x j))
    proveStatement "eigenvalueBounds" statement (← `(tactic| (
      rw [$(← ofRows A M Aq):term]
      simp only [Matrix.of_apply]
      refine ⟨fun x ↦ ⟨?_, ?_⟩, ?_, ?_⟩
      · have h := $(← exprToSyntax lower) x
        push_cast at h
        exact h
      · have h := $(← exprToSyntax upper) x
        push_cast at h
        exact h
      · have h := $(← exprToSyntax below)
        push_cast at h
        exact h
      · have h := $(← exprToSyntax above)
        push_cast at h
        exact h)))
  logReport ref {
    domain := s!"{n} × {n} symmetric real matrix"
    input := surfaceText input, inputType := "matrix"
    output :=
      s!"{Digits.renderSigned lo digits} ≤ λ_min, λ_max ≤ {Digits.renderSigned (-lo') digits}"
    outputType := "Rayleigh bounds" } #[
    computationNode "Certificate" #[
      m!"A - cI = L D Lᵀ and μI - A = L' D' L'ᵀ over ℚ, with nonnegative pivots",
      m!"x, y over ℚ with xᵀAx < (c + 10^-{digits}) |x|² and yᵀAy > (μ - 10^-{digits}) |y|²"],
    ← evidence "eigenvalueBounds" s!"Rayleigh bounds, sharp to 10^-{digits}" proposition proof]

end CAS.Command.Matrix

namespace CAS.Command

open Lean Elab Command

/-- `#cas [positiveDefinite] A` decides whether a square matrix `A` with rational entries is
positive definite and proves the answer.

## Theorem
The report proves `M.PosDef` or `¬ M.PosDef` for the matrix `M : Matrix (Fin n) (Fin n) ℝ` with
the entries of `A` and Mathlib's `Matrix.PosDef`, which includes symmetry. The answer `True`
comes from an exact factorization `A = L D Lᵀ` over `ℚ` with positive pivots
(`CAS.Analysis.Matrix.posDef_of_ldlCheck`). The answer `False` names a rational vector `x ≠ 0`
with `xᵀ A x ≤ 0` (`CAS.Analysis.Matrix.not_posDef_of_quadFormCheck`), or says that `A` is not
symmetric. The kernel checks the factorization or the vector.

## Conditions and limits
`A` is a square matrix literal `!![a, b; c, d]` or a list of rows `[[a, b], [c, d]]`, and each
entry is a closed rational expression such as `-3/2`, `0.25` or `1/10^15`.

## Options
None.

## Examples
```lean
#cas [positiveDefinite] !![2, 1; 1, 2]
```
```output
Output (Boolean): True
```
```lean
#cas [positiveDefinite] !![1, 2; 2, 1]
```
```output
Output (Boolean): False (xᵀAx ≤ 0 for x = [-2, 1])
```
```lean
#cas [positiveDefinite] !![1, 2; 3, 4]
```
```output
Output (Boolean): False (not symmetric)
```

## In a proof
```lean
theorem posDef_det_pos (h : (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ).PosDef) :
    0 < (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ).det :=
  h.det_pos
```
A proof can take the printed theorem as a hypothesis and use Mathlib's consequences of positive
definiteness, as here `Matrix.PosDef.det_pos`.

## See also
Mathematica `PositiveDefiniteMatrixQ`, SymPy `Matrix.is_positive_definite`. The modes
`eigenvalueBounds` and `eigenvalues`.

## Possible issues
```lean
#cas [positiveDefinite] !![1, 1; 1, 1]
```
```output
Output (Boolean): False (xᵀAx ≤ 0 for x = [-1, 1])
```
The matrix is positive semidefinite but not definite: the vector `x` has `A *ᵥ x = 0`.
`#cas [eigenvalueBounds] A` bounds the eigenvalues of a symmetric matrix.
```lean
#cas [positiveDefinite] !![1, 2, 3; 4, 5, 6]
```
```output
positiveDefinite: the matrix must be square
```
Positive definiteness is defined for square matrices only.
-/
syntax (name := casPositiveDefiniteCommand) "#cas" "[" &"positiveDefinite" "]" term : command

/-- `#cas [eigenvalueBounds] A` computes the smallest and the largest eigenvalue of a symmetric
matrix `A` with rational entries, rounded outward to `d` decimal places, and proves the bounds and
that they are sharp.

## Theorem
With `Q x = ∑ i, ∑ j, A i j * x i * x j` for the real matrix `A` and the printed decimals `c` and
`μ`, the report proves three facts over `ℝ`:
- `c * ∑ i, x i ^ 2 ≤ Q x ∧ Q x ≤ μ * ∑ i, x i ^ 2` for every `x : Fin n → ℝ`;
- `Q x < (c + 10 ^ (-d)) * ∑ i, x i ^ 2` for some `x`;
- `(μ - 10 ^ (-d)) * ∑ i, x i ^ 2 < Q x` for some `x`.

The theorem writes `Q x` out, and `c + 10 ^ (-d)` and `μ - 10 ^ (-d)` as decimals. So `c` is the
smallest eigenvalue rounded down to `d` places and `μ` the largest one rounded up. Both come from
bisection on the grid `10 ^ (-d) ℤ`. The kernel checks exact factorizations `L D Lᵀ` over `ℚ`
with nonnegative pivots of `A - c I` and `μ I - A`, and the two rational vectors.

## Conditions and limits
`A` is a symmetric square matrix literal `!![a, b; c, d]` or a list of rows `[[a, b], [c, d]]`,
and each entry is a closed rational expression such as `-3/2`, `0.25` or `1/10^15`.

## Options
`(digits := d)`, written `#cas (digits := d) [eigenvalueBounds] A`: the number `d` of decimal
places, `6` by default, between `1` and `cas.maxDigits` (`2000` by default).

## Examples
```lean
#cas [eigenvalueBounds] !![2, 1; 1, 2]
```
```output
Output (Rayleigh bounds): 1.000000 ≤ λ_min, λ_max ≤ 3.000000
```
```lean
#cas [eigenvalueBounds] !![4, 1, 0; 1, 3, 1; 0, 1, 2]
```
```output
Output (Rayleigh bounds): 1.267949 ≤ λ_min, λ_max ≤ 4.732051
```
```lean
#cas (digits := 3) [eigenvalueBounds] !![4, 1, 0; 1, 3, 1; 0, 1, 2]
```
```output
Output (Rayleigh bounds): 1.267 ≤ λ_min, λ_max ≤ 4.733
```

## In a proof
```lean
theorem rayleigh_lower
    (h : ∀ x : Fin 2 → ℝ,
      1.000000 * ∑ i, x i ^ 2 ≤ ∑ i, ∑ j, !![(2 : ℝ), 1; 1, 2] i j * x i * x j ∧
        ∑ i, ∑ j, !![(2 : ℝ), 1; 1, 2] i j * x i * x j ≤ 3.000000 * ∑ i, x i ^ 2)
    (x : Fin 2 → ℝ) :
    ∑ i, x i ^ 2 ≤ ∑ i, ∑ j, !![(2 : ℝ), 1; 1, 2] i j * x i * x j := by
  have e : (1.000000 : ℝ) = 1 := by norm_num
  have h₁ := (h x).1
  rw [e, one_mul] at h₁
  exact h₁
```
A proof can take the first part of the printed theorem as a hypothesis and use its lower bound, as
here.

## See also
Mathematica `Eigenvalues` with `N`, SymPy `Matrix.eigenvals`. The modes `eigenvalues` and
`positiveDefinite`.

## Possible issues
```lean
#cas [eigenvalueBounds] !![1, 2; 3, 4]
```
```output
eigenvalueBounds needs a symmetric matrix
```
The bounds are for symmetric matrices. `#cas [eigenvalues] A` takes every square matrix.
```lean
#cas (digits := 0) [eigenvalueBounds] !![2, 1; 1, 2]
```
```output
eigenvalueBounds accepts between 1 and 2000 digits
```
The number of places lies between `1` and `cas.maxDigits`.
-/
syntax (name := casEigenvalueBoundsCommand)
  "#cas" optConfig "[" &"eigenvalueBounds" "]" term : command

elab_rules : command
  | `(#cas [positiveDefinite] $m:term) => Matrix.logPosDef m m
  | `(#cas $cfg:optConfig [eigenvalueBounds] $m:term) => do
      Matrix.logEigenBounds m (← parseDigitsOption "eigenvalueBounds" cfg 6) m

end CAS.Command
