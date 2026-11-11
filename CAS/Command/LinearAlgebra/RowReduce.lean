/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.LinearAlgebra.Basic

/-!
# Row reduction: `#cas [rowReduce]`, `[matrixRank]`, `[nullSpace]`, `[linearSolve]`

One exact Gauss–Jordan elimination `E A = R` serves Mathematica's `RowReduce`, `MatrixRank`,
`NullSpace` and `LinearSolve` for matrices with rational entries. The statements are about
Mathlib's matrices over `ℚ`:

* `rowReduce`: `E * A = R ∧ E.det ≠ 0 ∧ R.IsReducedRowEchelon`, which determines `R`;
* `matrixRank`: `A.rank = r`, from a rank factorization `A = C F` with `C` the pivot columns
  (`Matrix.rank_mul_le_right`, `Matrix.rank_le_height`) and an `r × r` submatrix with nonzero
  determinant (`Matrix.rank_of_det_ne_zero`, `Matrix.rank_submatrix_le`);
* `nullSpace`: vectors `V i` with `A *ᵥ V i = 0`, linearly independent, spanning every solution
  of `A *ᵥ x = 0`;
* `linearSolve (A, b)`: `A *ᵥ x₀ = b` and `A *ᵥ x = b ↔ ∃ c, x = x₀ + ∑ i, c i • V i`, or, for an
  inconsistent system, `¬ ∃ x, A *ᵥ x = b`.

## Implementation notes

The elimination is `QMatrix.rowReduce` of `CAS/Command/LinearAlgebra/Basic.lean`, Gauss-Jordan
with the first nonzero pivot of each column; it proposes `R`, the row operations `E` and the pivot
columns. The kernel evaluates `E * A = R` and the three clauses of `Matrix.IsReducedRowEchelon`
(`reducedRowEchelonProof`), and `norm_det` proves `E.det ≠ 0`. For the rank we check the
factorization `A = C F` by kernel evaluation and take the rows of the nonsingular minor from a
second elimination, of `Cᵀ` (`rankScript`).

A null space vector has `1` at its free column and `0` at the other free columns (`nullBasis`).
So the vectors are independent by evaluation at the free columns, and the coefficients of an `x`
with `A *ᵥ x = 0` are its own free coordinates. Equations between literals are decided by kernel
evaluation. Each coordinate of a statement about all vectors `x`, and the inconsistency of a
system, is proved from the coordinates of `A *ᵥ x` by `linarith`, which finds the combination of
the coordinates by itself: the elimination's coefficients are not passed to it. The converse
direction of `linearSolve` is a ring identity (`ring1`), or a kernel evaluation when the solution
is unique.
-/

public meta section

namespace CAS.Command.LinearAlgebra

open Lean Elab Command Meta Term
open CAS.Command.InfoView
open CAS.Command.Algebra (natTerm ratText proveStatement)

/-- `(k : Fin n)` as a term. -/
def finTerm (k n : Nat) : TermElabM (TSyntax `term) := `(($(natTerm k) : Fin $(natTerm n)))

/-- The map `![i₀, i₁, …] : Fin r → Fin n`. -/
def indexMapTerm (indices : Array Nat) (n : Nat) : TermElabM (TSyntax `term) := do
  let entries ← indices.mapM fun k ↦ finTerm k n
  `((![$entries,*] : Fin $(natTerm indices.size) → Fin $(natTerm n)))

/-- The family `![v₀, v₁, …] : Fin k → Fin n → ℚ`. -/
def familyTerm (vectors : Array (Array ℚ)) (n : Nat) : TermElabM (TSyntax `term) := do
  let rows ← vectors.mapM fun v ↦ do
    let entries ← v.mapM ratTerm
    `(![$entries,*])
  `((![$rows,*] : Fin $(natTerm vectors.size) → Fin $(natTerm n) → ℚ))

/-- The proof that `R` (a literal) is in reduced row echelon form, by kernel evaluation of its
three clauses. -/
def reducedRowEchelonProof : TermElabM (TSyntax `term) :=
  `(⟨by unfold Matrix.IsRowEchelon; simp only [Matrix.of_apply]; decide +kernel,
    by intro i c; simp only [Matrix.IsLeadingEntry, Matrix.of_apply]; revert i c; decide +kernel,
    by
      intro i₁ i₂ c
      simp only [Matrix.IsLeadingEntry, Matrix.of_apply]
      revert i₁ i₂ c
      decide +kernel⟩)

/-- The tactic proving `d ≠ 0` for a determinant of a literal. -/
def detNeZeroTactic : TermElabM (TSyntax `tactic) :=
  `(tactic| first | (simp only [norm_det]; norm_num) | simp only [norm_det])

/-- Hypotheses `h₀ … h_{m-1}` with the coordinates of `hx : A *ᵥ x = b`, expanded. -/
def coordinateFacts (m : Nat) (hx : TSyntax `ident) : TermElabM (TSyntax `tactic) := do
  let names := (List.range m).toArray.map fun i ↦ mkIdent (Name.mkSimple s!"h{i}")
  let mut script ← `(tactic| skip)
  for (h, i) in names.zipIdx do
    let fact ← `(tactic| have $h:ident := congrFun $hx $(← finTerm i m))
    script ← `(tactic| ($script:tactic; $fact:tactic))
  `(tactic| (
    $script:tactic
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero] at $names*
    norm_num at $names*))

/-- The tactic proving `LinearIndependent ℚ V` for a null space basis: at its free coordinate
each vector is `1` and the others are `0`. -/
def independenceTactic (free : Array Nat) (n : Nat) : TermElabM (TSyntax `tactic) := do
  let names := (List.range free.size).toArray.map fun i ↦ mkIdent (Name.mkSimple s!"e{i}")
  let g := mkIdent `g
  let hg := mkIdent `hg
  let i := mkIdent `i
  let mut script ← `(tactic| (rw [Fintype.linearIndependent_iff]; intro $g $hg $i))
  for (e, f) in names.zip free do
    let fact ← `(tactic| have $e:ident := congrFun $hg $(← finTerm f n))
    script ← `(tactic| ($script:tactic; $fact:tactic))
  `(tactic| (
    $script:tactic
    simp [Fin.sum_univ_succ] at $names*
    fin_cases $i:ident <;> first | (simp; linarith) | linarith | simp_all))

/-- The tactic proving `x = ∑ i, c i • V i` (or `x = x₀ + …`) coordinatewise after the
coordinate facts are in context. -/
def coordinatewiseTactic : TermElabM (TSyntax `tactic) := do
  let j := mkIdent `j
  `(tactic| (funext $j:ident; fin_cases $j:ident <;>
    simp [Fin.sum_univ_succ, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;>
    linarith))

/-- Run `#cas [rowReduce] A`. -/
def logRowReduce (ref : Syntax) (input : Syntax) : CommandElabM Unit := do
  let A ← parseQMatrix input
  let (R, E, pivots) := A.rowReduce
  let (proposition, proof) ← liftTermElabM do
    let At ← matrixTerm A A.rows A.cols
    let Rt ← matrixTerm R A.rows A.cols
    let Et ← matrixTerm E A.rows A.rows
    let rref ← reducedRowEchelonProof
    proveStatement "rowReduce"
      (← `($Et * $At = $Rt ∧ Matrix.det $Et ≠ 0 ∧ Matrix.IsReducedRowEchelon $Rt))
      (← `(tactic| exact ⟨by decide +kernel, by $(← detNeZeroTactic):tactic, $rref⟩))
  logReport ref {
    domain := matrixDomain A
    input := A.text
    inputType := "matrix"
    output := R.text
    outputType := s!"reduced row echelon form, pivot columns {pivots.toList}"
  } #[← evidence "rowReduce" "Row operations E with E * A = R" proposition proof]

/-- The rank of `A` and a script proving `Matrix.rank At = r` for a term `At` denoting the
literal `A`. -/
def rankScript (A : QMatrix) (At : TSyntax `term) : TermElabM (Nat × TSyntax `tactic) := do
  let (R, _, pivots) := A.rowReduce
  let m := A.rows
  let n := A.cols
  let r := pivots.size
  if r = 0 then
    return (0, ← `(tactic| (rw [show $At = 0 by decide +kernel]; exact Matrix.rank_zero)))
  let C : QMatrix := A.map fun row ↦ pivots.map fun j ↦ row.getD j 0
  let F : QMatrix := R.extract 0 r
  -- Independent rows of `C`: the pivot columns of `Cᵀ`.
  let (_, _, rowsSel) := C.transpose.rowReduce
  let S : QMatrix := rowsSel.map fun i ↦ pivots.map fun j ↦ A.get i j
  let Ct ← matrixTerm C m r
  let Ft ← matrixTerm F r n
  let St ← matrixTerm S r r
  let rowsT ← indexMapTerm rowsSel m
  let colsT ← indexMapTerm pivots n
  return (r, ← `(tactic| (
    apply le_antisymm
    · calc Matrix.rank $At = Matrix.rank ($Ct * $Ft) := by
            rw [show $Ct * $Ft = $At by decide +kernel]
        _ ≤ Matrix.rank $Ft := Matrix.rank_mul_le_right _ _
        _ ≤ $(natTerm r) := Matrix.rank_le_height _
    · have hS : Matrix.det (Matrix.submatrix $At $rowsT $colsT) ≠ 0 := by
        rw [show Matrix.submatrix $At $rowsT $colsT = $St by decide +kernel]
        $(← detNeZeroTactic):tactic
      have hle := Matrix.rank_submatrix_le $At $rowsT $colsT
      rw [Matrix.rank_of_det_ne_zero hS, Fintype.card_fin] at hle
      exact hle)))

/-- Run `#cas [matrixRank] A`. -/
def logRank (ref : Syntax) (input : Syntax) : CommandElabM Unit := do
  let A ← parseQMatrix input
  let (proposition, proof, r) : Lean.Expr × Lean.Expr × Nat ← liftTermElabM do
    let At ← matrixTerm A A.rows A.cols
    let (r, script) ← rankScript A At
    let (a, b) ← proveStatement "matrixRank" (← `(Matrix.rank $At = $(natTerm r))) script
    pure (a, b, r)
  logReport ref {
    domain := matrixDomain A
    input := A.text
    inputType := "matrix"
    output := s!"{r}"
    outputType := "rank"
  } #[← evidence "matrixRank" "Rank from a factorization and a nonsingular minor" proposition
      proof]

/-- The statement and proof script that `V` is a basis of the null space of `A`. With `display`,
the statement names the matrix by that term (such as `B - λ • 1`), which the proof first rewrites
to the literal `A` by kernel evaluation. -/
def nullSpaceProof (A R : QMatrix) (pivots : Array Nat) (display : Option (TSyntax `term) := none) :
    TermElabM (Array (Array ℚ) × TSyntax `term × TSyntax `tactic) := do
  let m := A.rows
  let n := A.cols
  let V := R.nullBasis pivots
  let free := (List.range n).toArray.filter (!pivots.contains ·)
  let literal ← matrixTerm A m n
  let At := display.getD literal
  let rewrite ← match display with
    | some d => `(tactic| rw [show $d = $literal by decide +kernel])
    | none => `(tactic| skip)
  let x := mkIdent `x
  let hx := mkIdent `hx
  let facts ← coordinateFacts m hx
  let coordinatewise ← coordinatewiseTactic
  if V.isEmpty then
    let statement ← `(∀ x : Fin $(natTerm n) → ℚ, Matrix.mulVec $At x = 0 → x = 0)
    return (V, statement, ← `(tactic| (
      $rewrite:tactic
      intro $x $hx
      $facts:tactic
      $coordinatewise:tactic)))
  let Vt ← familyTerm V n
  let k := V.size
  let statement ← `((∀ i, Matrix.mulVec $At ($Vt i) = 0) ∧ LinearIndependent ℚ $Vt ∧
    ∀ x : Fin $(natTerm n) → ℚ, Matrix.mulVec $At x = 0 →
      ∃ c : Fin $(natTerm k) → ℚ, x = ∑ i, c i • $Vt i)
  let witness ← free.mapM fun f ↦ do `($x:ident $(← finTerm f n))
  let independence ← independenceTactic free n
  let script ← `(tactic| (
    $rewrite:tactic
    refine ⟨by decide +kernel, by $independence:tactic, ?_⟩
    intro $x $hx
    $facts:tactic
    refine ⟨![$witness,*], ?_⟩
    $coordinatewise:tactic))
  return (V, statement, script)

/-- Run `#cas [nullSpace] A`. -/
def logNullSpace (ref : Syntax) (input : Syntax) : CommandElabM Unit := do
  let A ← parseQMatrix input
  let (R, _, pivots) := A.rowReduce
  let (V, proposition, proof) ← liftTermElabM do
    let (V, statement, script) ← nullSpaceProof A R pivots
    let (a, b) ← proveStatement "nullSpace" statement script
    pure (V, a, b)
  logReport ref {
    domain := matrixDomain A
    input := A.text
    inputType := "matrix"
    output := if V.isEmpty then "[] (only the zero vector)"
      else "[" ++ ", ".intercalate (V.toList.map vectorText) ++ "]"
    outputType := s!"basis of the null space, dimension {V.size}"
  } #[← evidence "nullSpace" "Basis of the null space" proposition proof]

/-- Run `#cas [linearSolve] (A, b)`. -/
def logLinearSolve (ref : Syntax) (left right : Syntax) : CommandElabM Unit := do
  let A ← parseQMatrix left
  let b ← parseQVector right
  let m := A.rows
  let n := A.cols
  unless b.size = m do throwErrorAt right "linearSolve: the right side has {b.size} entries, \
    the matrix {m} rows"
  let augmented : QMatrix := A.zipWith (fun row c ↦ row.push c) b
  let (R, _, pivots) := augmented.rowReduce
  let (proposition, proof, shown) : Lean.Expr × Lean.Expr × String ← liftTermElabM do
    let At ← matrixTerm A m n
    let bt ← vectorTerm b
    let x := mkIdent `x
    let hx := mkIdent `hx
    let c := mkIdent `c
    let facts ← coordinateFacts m hx
    if pivots.contains n then
      let (a, c) ← proveStatement "linearSolve"
        (← `(¬ ∃ x : Fin $(natTerm n) → ℚ, Matrix.mulVec $At x = $bt))
        (← `(tactic| (rintro ⟨$x:ident, $hx:ident⟩; $facts:tactic; linarith)))
      pure (a, c, "no solution")
    else
      let RA : QMatrix := R.map (·.extract 0 n)
      let x₀ := R.particularSolution pivots n
      let V := RA.nullBasis pivots
      let free := (List.range n).toArray.filter (!pivots.contains ·)
      let x₀t ← vectorTerm x₀
      let coordinatewise ← coordinatewiseTactic
      let i := mkIdent `i
      let back ← `(tactic| (funext $i:ident; fin_cases $i:ident <;>
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Finset.sum_apply, Pi.add_apply,
          Pi.smul_apply, smul_eq_mul] <;> ring1))
      if V.isEmpty then
        let (a, c) ← proveStatement "linearSolve"
          (← `(∀ x : Fin $(natTerm n) → ℚ, Matrix.mulVec $At x = $bt ↔ x = $x₀t))
          (← `(tactic| exact fun $x:ident ↦
            ⟨fun $hx:ident ↦ by $facts:tactic; $coordinatewise:tactic,
              fun hsol ↦ by rw [hsol]; decide +kernel⟩))
        pure (a, c, vectorText x₀)
      else
        let Vt ← familyTerm V n
        let k := V.size
        let witness ← free.mapM fun f ↦ do `($x:ident $(← finTerm f n))
        let independence ← independenceTactic free n
        let (a, c) ← proveStatement "linearSolve"
          (← `(Matrix.mulVec $At $x₀t = $bt ∧ LinearIndependent ℚ $Vt ∧
            ∀ x : Fin $(natTerm n) → ℚ, Matrix.mulVec $At x = $bt ↔
              ∃ c : Fin $(natTerm k) → ℚ, x = $x₀t + ∑ i, c i • $Vt i))
          (← `(tactic| (
            refine ⟨by decide +kernel, by $independence:tactic,
              fun $x:ident ↦ ⟨fun $hx:ident ↦ ?_, ?_⟩⟩
            · $facts:tactic
              refine ⟨![$witness,*], ?_⟩
              $coordinatewise:tactic
            · rintro ⟨$c:ident, hsol⟩
              rw [hsol]
              $back:tactic)))
        pure (a, c, s!"{vectorText x₀} + span of " ++ "[" ++
          ", ".intercalate (V.toList.map vectorText) ++ "]")
  logReport ref {
    domain := matrixDomain A
    input := s!"{A.text} . x = {vectorText b}"
    inputType := "linear system"
    output := shown
    outputType := "all solutions"
  } #[← evidence "linearSolve" "Solution set" proposition proof]

end CAS.Command.LinearAlgebra

namespace CAS.Command

open Lean Elab Command

/-- `#cas [rowReduce] A` computes the reduced row echelon form `R` of a matrix `A` with rational
entries and proves it.

## Theorem
The report proves `E * A = R ∧ E.det ≠ 0 ∧ R.IsReducedRowEchelon` over `ℚ`, for the matrix `E` of
the row operations of an exact Gauss-Jordan elimination and Mathlib's
`Matrix.IsReducedRowEchelon`. These three facts determine `R`. The kernel evaluates the product
and the echelon conditions, and `norm_det` the determinant. The report also prints the pivot
columns, numbered from `0`.

## Conditions and limits
`A` is a matrix literal `!![a, b; c, d]` or a list of rows `[[a, b], [c, d]]` of any shape, and
each entry is a closed rational expression such as `-3/2`, `0.25` or `1/10^15`.

## Options
None.

## Examples
```lean
#cas [rowReduce] !![1, 2, 3; 4, 5, 6; 7, 8, 9]
```
```output
Output (reduced row echelon form, pivot columns [0, 1]): !![1, 0, -1; 0, 1, 2; 0, 0, 0]
```
```lean
#cas [rowReduce] !![0, 2, 4, 1; 1, 1, 1, 1; 2, 4, 6, 3]
```
```output
Output (reduced row echelon form, pivot columns [0, 1]):
!![1, 0, -1, 1/2; 0, 1, 2, 1/2; 0, 0, 0, 0]
```

## In a proof
```lean
theorem rowReduce_certificate :
    !![(-(5 / 3) : ℚ), 2 / 3, 0; 4 / 3, -(1 / 3), 0; 1, -2, 1] * !![1, 2, 3; 4, 5, 6; 7, 8, 9] =
      !![1, 0, -1; 0, 1, 2; 0, 0, 0] := by
  decide +kernel
```
The matrix `E` comes from the theorem in the report of the first example, and kernel evaluation,
the proof of the report, checks the product.

## See also
Mathematica `RowReduce`, SymPy `Matrix.rref`. The modes `matrixRank`, `nullSpace` and
`linearSolve`.

## Possible issues
```lean
#cas [rowReduce] (!![1, 2; 3, 4], ![5, 6])
```
```output
expected a matrix `!![a, b; c, d]` or `[[a, b], [c, d]]`
```
The mode takes one matrix. For the system `A *ᵥ x = b`, reduce the augmented matrix
`!![1, 2, 5; 3, 4, 6]`, or solve it with `#cas [linearSolve] (A, b)`.
-/
syntax (name := casRowReduceCommand) "#cas" "[" &"rowReduce" "]" term : command

/-- `#cas [matrixRank] A` computes the rank of a matrix `A` with rational entries and proves it.

## Theorem
The report proves `A.rank = r` for Mathlib's `Matrix.rank` over `ℚ`. A rank factorization
`A = C F`, with `C` the pivot columns of `A`, bounds the rank from above, and an `r × r` submatrix
with nonzero determinant bounds it from below (`Matrix.rank_of_det_ne_zero`).

## Conditions and limits
`A` is a matrix literal `!![a, b; c, d]` or a list of rows `[[a, b], [c, d]]` of any shape, and
each entry is a closed rational expression such as `-3/2`, `0.25` or `1/10^15`.

## Options
None.

## Examples
```lean
#cas [matrixRank] !![1, 2, 3; 4, 5, 6; 7, 8, 9]
```
```output
Output (rank): 2
```
```lean
#cas [matrixRank] !![1, 2, 3, 4; 2, 4, 6, 8]
```
```output
Output (rank): 1
```
```lean
#cas [matrixRank] !![0, 0; 0, 0]
```
```output
Output (rank): 0
```

## In a proof
```lean
theorem rank_three : Matrix.rank !![(1 : ℚ), 2, 3; 4, 5, 6; 7, 8, 9] = 2 := by
  cas
```

## See also
Mathematica `MatrixRank`, SymPy `Matrix.rank`. The modes `rowReduce`, `nullSpace` and `det`.

## Possible issues
```lean
#cas [matrixRank] ![1, 2, 3]
```
```output
expected a matrix `!![a, b; c, d]` or `[[a, b], [c, d]]`
```
A vector is written as a matrix with one row, `!![1, 2, 3]`, or with one column, `!![1; 2; 3]`.
-/
syntax (name := casMatrixRankCommand) "#cas" "[" &"matrixRank" "]" term : command

/-- `#cas [nullSpace] A` computes a basis of the null space of a matrix `A` with rational entries
and proves that it is one.

## Theorem
For the printed vectors `V i` the report proves, over `ℚ`, `A.mulVec (V i) = 0` for each `i`,
`LinearIndependent ℚ V`, and `∀ x, A.mulVec x = 0 → ∃ c, x = ∑ i, c i • V i`. When the null space
is zero it prints `[] (only the zero vector)` and proves `∀ x, A.mulVec x = 0 → x = 0`. The
vectors come from the free columns of the reduced row echelon form, and `linarith` proves the
statement about every `x` from the coordinates of `A.mulVec x`.

## Conditions and limits
`A` is a matrix literal `!![a, b; c, d]` or a list of rows `[[a, b], [c, d]]` of any shape, and
each entry is a closed rational expression such as `-3/2`, `0.25` or `1/10^15`. The printed
dimension is the number of columns of `A` minus its rank.

## Options
None.

## Examples
```lean
#cas [nullSpace] !![1, 2, 3; 2, 4, 6]
```
```output
Output (basis of the null space, dimension 2): [![-2, 1, 0], ![-3, 0, 1]]
```
```lean
#cas [nullSpace] !![1, 2; 3, 4]
```
```output
Output (basis of the null space, dimension 0): [] (only the zero vector)
```

## In a proof
```lean
theorem nullSpace_vector : !![(1 : ℚ), 2, 3; 2, 4, 6].mulVec ![-2, 1, 0] = 0 := by
  cas
```

## See also
Mathematica `NullSpace`, SymPy `Matrix.nullspace`. The modes `linearSolve`, `matrixRank`,
`rowReduce` and `eigenvectors`.

## Possible issues
```lean
#cas [nullSpace] (!![1, 2; 3, 4], ![0, 0])
```
```output
expected a matrix `!![a, b; c, d]` or `[[a, b], [c, d]]`
```
The mode takes the matrix alone. `#cas [linearSolve] (A, b)` solves a system with a right side.
-/
syntax (name := casNullSpaceCommand) "#cas" "[" &"nullSpace" "]" term : command

/-- `#cas [linearSolve] (A, b)` finds all solutions `x` of the linear system `A *ᵥ x = b` with
rational entries and proves that there are no others.

## Theorem
Over `ℚ` the report proves one of three statements:
- one solution `x₀`: `∀ x, A.mulVec x = b ↔ x = x₀`;
- a particular solution `x₀` plus the span of null space vectors `V i`: `A.mulVec x₀ = b`,
  `LinearIndependent ℚ V` and `∀ x, A.mulVec x = b ↔ ∃ c, x = x₀ + ∑ i, c i • V i`;
- no solution: `¬∃ x, A.mulVec x = b`.

The equations between literals are decided by kernel evaluation, and `linarith` proves the
statements about every `x` from the coordinates of `A.mulVec x`.

## Conditions and limits
`A` is a matrix literal `!![a, b; c, d]` or a list of rows `[[a, b], [c, d]]` of any shape, and
`b` is a vector `![a, b]` or `[a, b]` with one entry for each row of `A`. Each entry is a closed
rational expression such as `-3/2`, `0.25` or `1/10^15`.

## Options
None.

## Examples
```lean
#cas [linearSolve] (!![1, 2; 3, 4], ![5, 6])
```
```output
Output (all solutions): ![-4, 9/2]
```
```lean
#cas [linearSolve] (!![1, 2, 3; 2, 4, 6], ![1, 2])
```
```output
Output (all solutions): ![1, 0, 0] + span of [![-2, 1, 0], ![-3, 0, 1]]
```
```lean
#cas [linearSolve] (!![1, 2, 3; 2, 4, 6], ![1, 3])
```
```output
Output (all solutions): no solution
```

## In a proof
```lean
theorem linearSolve_check : !![(1 : ℚ), 2; 3, 4].mulVec ![-4, 9 / 2] = ![5, 6] := by
  cas
```

## See also
Mathematica `LinearSolve`, SymPy `linsolve`. The modes `nullSpace`, `rowReduce`, `inverse` and
`solve`, which solves systems of equations in named variables.

## Possible issues
```lean
#cas [linearSolve] (!![1, 2; 3, 4], ![5, 6, 7])
```
```output
linearSolve: the right side has 3 entries, the matrix 2 rows
```
The right side `b` has one entry for each row of `A`.
```lean
#cas [linearSolve] !![1, 2; 3, 4]
```
```output
linearSolve: expected a pair `(A, b)`
```
The mode takes the pair `(A, b)`. `#cas [nullSpace] A` solves `A *ᵥ x = 0`.
-/
syntax (name := casLinearSolveCommand) "#cas" "[" &"linearSolve" "]" term : command

elab_rules : command
  | `(#cas [rowReduce] $A:term) => LinearAlgebra.logRowReduce A A
  | `(#cas [matrixRank] $A:term) => LinearAlgebra.logRank A A
  | `(#cas [nullSpace] $A:term) => LinearAlgebra.logNullSpace A A
  | `(#cas [linearSolve] $e:term) => do
      match e with
      | `(($A, $b)) => LinearAlgebra.logLinearSolve e A b
      | _ => throwErrorAt e "linearSolve: expected a pair `(A, b)`"

end CAS.Command
