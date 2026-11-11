/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.Algebra.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Echelon.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormDet
public meta import Mathlib.Tactic.NormDet
public meta import CAS.Expr.RationalEvaluation
public meta import CAS.Tactic.Classify

/-!
# Exact linear algebra over `ℚ` for the matrix commands

The matrix commands (`det`, `inverse`, `rowReduce`, `matrixRank`, `nullSpace`, `linearSolve`,
`characteristicPolynomial`, `eigenvectors`, `positiveDefinite`, `eigenvalueBounds`, …) read a
matrix literal `!![a, b; c, d]` whose entries are closed rational expressions such as `-3/2`,
`0.25` or `1/10^15` (`parseQMatrix`) into a `QMatrix`, an array of rational rows. They compute
with exact Gauss-Jordan elimination (`rowReduce`), the exact symmetric elimination `A = L D Lᵀ`
(`ldl`) and the Faddeev-LeVerrier recursion for the characteristic polynomial (`charpoly`). The
terms of their statements (`matrixTerm`, `vectorTerm`) and the tactics for equations between
literals (`kernelDecide`, `detTactic`) are built here too.

## Implementation notes

Nothing computed here is trusted. The commands state their results about Mathlib's
`Matrix (Fin m) (Fin n) ℚ` and prove them in `CAS/Command/LinearAlgebra/Operations.lean`,
`CAS/Command/LinearAlgebra/RowReduce.lean`, `CAS/Command/LinearAlgebra/Eigen.lean` and
`CAS/Command/Matrix.lean`: equations between matrix literals by kernel evaluation
(`decide +kernel`), determinants by Mathlib's `norm_det`, null spaces and solution sets by
`linarith` from the coordinates of `A *ᵥ x`, the eigenspaces of irrational eigenvalues by
`CAS.Analysis.Matrix.eigenspace_basis`, and positive definiteness and Rayleigh bounds from the
factors of `ldl` by the checks of `CAS/Analysis/Matrix/PosDefCertificate.lean`.

The algorithms are the classical ones in exact arithmetic. We keep one elimination, `rowReduce`,
for inverses, ranks, null spaces and linear systems; `CAS/Command/Systems.lean`,
`CAS/Command/InverseLaplace.lean` and `CAS/Command/DSolveOrder.lean` use it too. `charpoly` runs
the recursion `M_k = A M_{k-1} + c_{n-k+1} I`, `c_{n-k} = -tr (A M_k) / k`. No determinant value
is computed here: `norm_det` computes it, or Hex's Bareiss elimination with `-Khex=on`
(`CASHex/LinearAlgebra.lean`).

## References

* Gene H. Golub and Charles F. Van Loan, *Matrix Computations*, 4th ed., The Johns Hopkins
  University Press, Baltimore, 2013, <https://doi.org/10.56021/9781421407944>. The standard
  reference for the `L D Lᵀ` factorization of `ldl`.
* Shui-Hung Hou, "Classroom Note: A Simple Proof of the Leverrier-Faddeev Characteristic
  Polynomial Algorithm", *SIAM Review* 40 (1998), no. 3, pp. 706-709,
  <https://doi.org/10.1137/S003614459732076X>. A proof of the recursion that `charpoly` runs.
-/
public meta section

namespace CAS.Command.LinearAlgebra

open Lean Elab Command Meta Term
open CAS.Command.Algebra (natTerm ratText proveStatement checkedEvidence)

/-- A rational matrix stored by rows. -/
abbrev QMatrix := Array (Array ℚ)

namespace QMatrix

/-- The number of rows. -/
def rows (A : QMatrix) : Nat := A.size

/-- The number of columns. -/
def cols (A : QMatrix) : Nat := (A.getD 0 #[]).size

/-- Entry `(i, j)`. -/
def get (A : QMatrix) (i j : Nat) : ℚ := (A.getD i #[]).getD j 0

/-- The identity of size `n`. -/
def identity (n : Nat) : QMatrix :=
  Array.ofFn fun (i : Fin n) ↦ Array.ofFn fun (j : Fin n) ↦ if i = j then 1 else 0

/-- `A B`. -/
def mul (A B : QMatrix) : QMatrix :=
  Array.ofFn fun (i : Fin A.rows) ↦ Array.ofFn fun (j : Fin B.cols) ↦
    (List.range A.cols).foldl (fun s k ↦ s + A.get i k * B.get k j) 0

/-- `Aᵀ`. -/
def transpose (A : QMatrix) : QMatrix :=
  Array.ofFn fun (j : Fin A.cols) ↦ Array.ofFn fun (i : Fin A.rows) ↦ A.get i j

/-- `A v`. -/
def mulVec (A : QMatrix) (v : Array ℚ) : Array ℚ :=
  Array.ofFn fun (i : Fin A.rows) ↦
    (List.range A.cols).foldl (fun s k ↦ s + A.get i k * v.getD k 0) 0

/-- `A - c I`. -/
def subScalar (A : QMatrix) (c : ℚ) : QMatrix :=
  A.mapIdx fun i row ↦ row.mapIdx fun j a ↦ if i = j then a - c else a

/-- The trace. -/
def trace (A : QMatrix) : ℚ := (List.range A.rows).foldl (fun s i ↦ s + A.get i i) 0

/-- The reduced row echelon form `R`, an invertible `E` with `E A = R`, and the pivot columns,
by Gauss–Jordan elimination with the first nonzero pivot of each column. Row `i` of `R` has its
leading `1` in column `pivots[i]`, the other entries of that column are `0`, and the rows after
the last pivot row are zero. This is the one elimination of the commands: inverses, ranks, null
spaces and the solutions of linear systems (`particularSolution`, `solve?`) are read off it. -/
def rowReduce (A : QMatrix) : QMatrix × QMatrix × Array Nat := Id.run do
  let m := A.rows
  let n := A.cols
  let mut R := A
  let mut E := identity m
  let mut pivots : Array Nat := #[]
  let mut row := 0
  for col in [0:n] do
    if row ≥ m then break
    let some p := (List.range (m - row)).map (· + row) |>.find? fun i ↦ R.get i col ≠ 0
      | continue
    -- Swap rows `p` and `row`.
    let rp := R[p]!
    let rr := R[row]!
    R := (R.set! p rr).set! row rp
    let ep := E[p]!
    let er := E[row]!
    E := (E.set! p er).set! row ep
    -- Scale the pivot row.
    let c := R.get row col
    R := R.set! row (R[row]!.map (· / c))
    E := E.set! row (E[row]!.map (· / c))
    -- Clear the column.
    for i in [0:m] do
      if i = row then continue
      let f := R.get i col
      if f = 0 then continue
      R := R.set! i ((R[i]!.zip R[row]!).map fun (a, b) ↦ a - f * b)
      E := E.set! i ((E[i]!.zip E[row]!).map fun (a, b) ↦ a - f * b)
    pivots := pivots.push col
    row := row + 1
  return (R, E, pivots)

/-- The solution of a linear system in `n` unknowns read off the reduced row echelon form `R`
of its augmented matrix `[A | b]` and the pivot columns `pivots` (from `rowReduce`): the unknown
of each pivot column takes the last entry of its row, and the free unknowns are `0`. It solves
the system whenever the system is consistent, that is when `n` is not a pivot column. -/
def particularSolution (R : QMatrix) (pivots : Array Nat) (n : Nat) : Array ℚ := Id.run do
  let mut v := Array.replicate n 0
  for (p, r) in pivots.zipIdx do v := v.set! p (R.get r n)
  return v

/-- A solution of `A x = b` in `n` unknowns, the rows of `A` read with `n` entries, by
`rowReduce` of the augmented matrix and `particularSolution`: `none` when the system is
inconsistent, and otherwise the solution whose free unknowns are `0`, which is the only solution
when all `n` columns are pivot columns. -/
def solve? (A : QMatrix) (b : Array ℚ) (n : Nat) : Option (Array ℚ) :=
  let augmented : QMatrix := (Array.range A.rows).map fun i ↦
    ((Array.range n).map fun j ↦ A.get i j).push (b.getD i 0)
  let (R, _, pivots) := rowReduce augmented
  if pivots.contains n then none else some (particularSolution R pivots n)

/-- The inverse of a square matrix, or `none` when it is singular. -/
def inverse? (A : QMatrix) : Option QMatrix :=
  let (R, E, _) := rowReduce A
  if R == identity A.rows then some E else none

/-- A basis of the null space from the reduced row echelon form: one vector per free column,
with `1` there, `0` at the other free columns, and minus the pivot rows' entries at the pivot
columns. -/
def nullBasis (R : QMatrix) (pivots : Array Nat) : Array (Array ℚ) := Id.run do
  let n := R.cols
  let free := (List.range n).filter (!pivots.contains ·)
  let mut out : Array (Array ℚ) := #[]
  for f in free do
    let mut v : Array ℚ := Array.replicate n 0
    v := v.set! f 1
    for (p, r) in pivots.zipIdx do
      v := v.set! p (-(R.get r f))
    out := out.push v
  return out

/-- The characteristic polynomial `det (X I - A)`, coefficients from the constant term up, by the
Faddeev–LeVerrier recursion. -/
def charpoly (A : QMatrix) : Array ℚ := Id.run do
  let n := A.rows
  let mut coefficients : Array ℚ := Array.replicate (n + 1) 0
  coefficients := coefficients.set! n 1
  let mut M : QMatrix := Array.replicate n (Array.replicate n 0)
  for k in [1:n + 1] do
    -- `M_k = A M_{k-1} + c_{n-k+1} I`, `c_{n-k} = -tr (A M_k) / k`.
    let previous := coefficients[n - k + 1]!
    M := (A.mul M).mapIdx fun i row ↦ row.mapIdx fun j a ↦ if i = j then a + previous else a
    let c := -(A.mul M).trace / (k : ℚ)
    coefficients := coefficients.set! (n - k) c
  return coefficients

/-- The first entry `(i, j)` of a square matrix, in row order, with `aᵢⱼ ≠ aⱼᵢ`, or `none` when
the matrix is symmetric. -/
def asymmetricEntry? (A : QMatrix) : Option (Nat × Nat) := Id.run do
  for i in [0:A.rows] do
    for j in [0:A.rows] do
      if A.get i j ≠ A.get j i then return some (i, j)
  return none

/-- The largest absolute row sum `maxᵢ ∑ⱼ |aᵢⱼ|`, a bound on the absolute value of every eigenvalue
of a square matrix. -/
def rowSumBound (A : QMatrix) : ℚ :=
  A.foldl (fun bound row ↦ max bound (row.foldl (fun s a ↦ s + |a|) 0)) 0

/-- The exact factorization `A = L D Lᵀ` of a symmetric matrix by symmetric elimination without
pivoting, with `L` unit lower triangular and the pivots `D`. A zero pivot whose column in the
Schur complement is zero is kept, with that column of `L` zero below the diagonal.

When `A` is not positive definite (with `strict`) or not positive semidefinite (without it), the
error is a rational vector `x` with `xᵀ A x ≤ 0` and `x ≠ 0`, respectively `xᵀ A x < 0`. At the
first pivot `d ≤ 0` (`d < 0` without `strict`) the vector `u = eⱼ` has `uᵀ S u = d` on the Schur
complement `S` of the leading `j × j` block. At a zero pivot with an entry `b ≠ 0` below it in row
`i`, `u = t eⱼ + eᵢ` with `t = -(sᵢᵢ + 1) / (2 b)` has `uᵀ S u = -1`. Back substitution in the
first `j` columns of `L` lifts `u` to `x` with `xᵀ A x = uᵀ S u`. -/
def ldl (A : QMatrix) (strict : Bool) : Except (Array ℚ) (QMatrix × Array ℚ) := Id.run do
  let n := A.rows
  -- `x` with `xₘ = uₘ` for `m ≥ j` and `(Lᵀ x)ₖ = 0` for `k < j`.
  let lift (L : QMatrix) (j : Nat) (u : Array ℚ) : Array ℚ := Id.run do
    let mut x := u
    for r' in [0:j] do
      let r := j - 1 - r'
      x := x.set! r (-((List.range n).foldl
        (fun s m ↦ if r < m then s + L.get m r * x.getD m 0 else s) 0))
    return x
  let unit (j : Nat) : Array ℚ := (Array.replicate n 0).set! j 1
  let mut L : QMatrix := identity n
  let mut D : Array ℚ := Array.replicate n 0
  for j in [0:n] do
    -- Column `j` of the Schur complement of the leading `j × j` block.
    let schur (i : Nat) : ℚ :=
      (List.range j).foldl (fun s k ↦ s - L.get i k * L.get j k * D.getD k 0) (A.get i j)
    let pivot := schur j
    D := D.set! j pivot
    if pivot < 0 || (strict && pivot = 0) then return .error (lift L j (unit j))
    if pivot = 0 then
      if let some i := ((List.range (n - j - 1)).map (· + j + 1)).find? (schur · ≠ 0) then
        let b := schur i
        let sii := (List.range j).foldl (fun s k ↦ s - L.get i k ^ 2 * D.getD k 0) (A.get i i)
        return .error (lift L j ((unit i).set! j (-(sii + 1) / (2 * b))))
    else
      for i in [j + 1:n] do
        L := L.set! i (L[i]!.set! j (schur i / pivot))
  return .ok (L, D)

/-- The matrix as text `!![a, b; c, d]`. -/
def text (A : QMatrix) : String :=
  "!![" ++ "; ".intercalate (A.toList.map fun row ↦ ", ".intercalate (row.toList.map ratText))
    ++ "]"

end QMatrix

/-- The domain line of a matrix report. -/
def matrixDomain (A : QMatrix) : String := s!"ℚ^({A.rows}×{A.cols})"

/-- A vector as text `![a, b]`. -/
def vectorText (v : Array ℚ) : String := "![" ++ ", ".intercalate (v.toList.map ratText) ++ "]"

/-- A rational as a term of `ℚ`. -/
def ratTerm (q : ℚ) : TermElabM (TSyntax `term) := do `(($(← ratSyntax q) : ℚ))

/-- The matrix as the term `(Matrix.of ![![a, …], …] : Matrix (Fin rows) (Fin cols) K)`, each
entry ascribed to the field `K`, such as `ℚ`, `ℝ` or `ℂ`. -/
def matrixTermOver {m : Type → Type} [Monad m] [MonadQuotation m] (A : QMatrix)
    (K : TSyntax `term) (rows : Nat := A.rows) (cols : Nat := A.cols) : m (TSyntax `term) := do
  let rowTerms ← A.mapM fun row ↦ do
    let entries ← row.mapM fun a ↦ do `(($(← ratSyntax a) : $K))
    `(![$entries,*])
  `((Matrix.of ![$rowTerms,*] : Matrix (Fin $(natTerm rows)) (Fin $(natTerm cols)) $K))

/-- The matrix as the term `Matrix.of ![![…], …] : Matrix (Fin m) (Fin n) ℚ`. -/
def matrixTerm (A : QMatrix) (rows cols : Nat) : TermElabM (TSyntax `term) := do
  matrixTermOver A (← `(ℚ)) rows cols

/-- The vector as the term `![…] : Fin n → ℚ`. -/
def vectorTerm (v : Array ℚ) : TermElabM (TSyntax `term) := do
  let entries ← v.mapM ratTerm
  `((![$entries,*] : Fin $(natTerm v.size) → ℚ))

/-- Strip parentheses. -/
partial def unparen (stx : Syntax) : Syntax :=
  match stx with
  | `(($inner)) => unparen inner
  | _ => stx

/-- Read a matrix or vector entry: a closed rational expression such as `-3/2`, `0.25` or
`1/10^15`. -/
def parseEntry (stx : Syntax) : CommandElabM ℚ := do
  let lowered := (← parseExpr stx).toVerifiedExprM? (m := Id) (ι' := Fin 0)
    (fun _ ↦ none) (fun exponent ↦ some exponent)
  match lowered.bind (Verified.Expr.evalRat? Fin.elim0) with
  | some q => return q
  | none => throwErrorAt stx "expected a rational number, such as -3/2, 0.25 or 1/10^15"

/-- Parse `!![a, b; c, d]` or `[[a, b], [c, d]]` into rational rows of equal length. -/
def parseQMatrix (stx : Syntax) : CommandElabM QMatrix := do
  let stx := unparen stx
  let rows : Array (Array Syntax) ← match stx with
    | `(!![$[$[$rows],*];*]) => pure (rows.map (·.map (·.raw)))
    | `([$[$rows],*]) => rows.mapM fun row ↦ match row with
        | `([$[$entries],*]) => pure (entries.map (·.raw))
        | _ => throwErrorAt row "expected a row `[a, b, …]`"
    | _ => throwErrorAt stx "expected a matrix `!![a, b; c, d]` or `[[a, b], [c, d]]`"
  if rows.isEmpty || rows[0]!.isEmpty then throwErrorAt stx "the matrix is empty"
  unless rows.all (·.size == rows[0]!.size) do
    throwErrorAt stx "the rows of the matrix have different lengths"
  rows.mapM fun row ↦ row.mapM parseEntry

/-- Parse a vector `![a, b]` or `[a, b]`. -/
def parseQVector (stx : Syntax) : CommandElabM (Array ℚ) := do
  let stx := unparen stx
  let entries : Array Syntax ← match stx with
    | `(![$[$entries],*]) => pure (entries.map (·.raw))
    | `([$[$entries],*]) => pure (entries.map (·.raw))
    | _ => throwErrorAt stx "expected a vector `![a, b, …]` or `[a, b, …]`"
  entries.mapM parseEntry

/-- The tactic deciding an equation between matrix or vector literals in the kernel. -/
def kernelDecide : TermElabM (TSyntax `tactic) := `(tactic| decide +kernel)

/-- The tactic evaluating a determinant of a literal with `norm_det`. -/
def detTactic : TermElabM (TSyntax `tactic) :=
  `(tactic| first | (simp only [norm_det]; done) | (simp only [norm_det]; norm_num))

/-- The determinant of the literal `At` as computed by Mathlib's `norm_det` simproc and read as a
rational, `none` when the result is not a numeral expression. With `-Khex=on`, `#cas [det]` goes
to the backend of `CASHex.LinearAlgebra`, Hex's Bareiss elimination, before this function;
SymLean itself has no elimination code for the determinant value. -/
def detByNormDet (At : TSyntax `term) : TermElabM (Option ℚ) := do
  let e ← elabTerm (← `(Matrix.det $At)) none
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let simprocs ← ({} : Simp.Simprocs).add `norm_det (post := true)
  let context ← Simp.mkContext {}
  let (result, _) ← Simp.main e context (methods := Simp.mkDefaultMethodsCore #[simprocs])
  Tactic.Classify.rationalLiteral? result.expr

/-- The report evidence of a proved proposition. -/
def evidence (operation label : String) (proposition proof : Lean.Expr) :
    CommandElabM MessageData :=
  liftTermElabM <| checkedEvidence operation label proposition proof

end CAS.Command.LinearAlgebra
