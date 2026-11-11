/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.IntervalEval.Range
public import CAS.Continuum.MatrixVerification.RowSum
public import CAS.Expr.Operators

/-!
# Interval verification of symbolic matrix expressions

The certified expression evaluator applied to finite-dimensional approximate-inverse
verification, in three layers:

* symbolic matrix multiplication and left-residual formation;
* an executable traversal which evaluates every entry of a `Fin n` matrix and fails if any entry
  cannot be enclosed; and
* an automatic row-sum checker whose successful result proves that the evaluated matrix is
  invertible at every point of the certified parameter domain.

## Main results

* `evalMatrix_leftResidual`: the symbolic residual `I - B A` evaluates to the real residual.
* `evalMatrix?_apply`, `evalMatrix?_eq_some_of_apply`: the fail-closed entrywise traversal
  succeeds exactly when every entry evaluates.
* `ApproximateInverseData.certify?`: the executable checker, returning the residual intervals
  only when the largest absolute row sum is strictly below `1`.
* `ApproximateInverseData.matrix_isUnitAt`: whenever `certify?` succeeds, the evaluated matrix
  is invertible at every point of the certified domain.

## Implementation notes

The mathematics is the Neumann-series lemma: if `‖I - B A‖_∞ < 1` in the maximum absolute row
sum norm, then `B A` is invertible, hence so is `A`. Here the entries of `I - B A` are symbolic
expressions in the parameters, and the interval evaluator bounds each of them uniformly over the
certified parameter domain, so one exact rational row-sum check proves invertibility at every
parameter value simultaneously.

The checker computes the largest exact rational absolute row sum itself. Search code may choose
the approximate inverse and the interval-evaluation context, but no proposed matrix norm enters
the trusted theorem. `matrix_isUnitAt` needs a proof that `certify?` returned `some`, so
successful expression evaluation and the strict Neumann threshold are both rechecked in Lean.

## References

* Siegfried M. Rump, "Verification methods: Rigorous results using floating-point arithmetic",
  *Acta Numerica* 19 (2010), pp. 287-449, <https://doi.org/10.1017/S096249291000005X>.
  Theorem 10.2 for approximate-inverse verification of invertibility.
-/

@[expose] public section

namespace CAS.Continuum.MatrixVerification

open CAS.Verified

namespace Expression

noncomputable section

/-! ## Symbolic matrix algebra -/

/-- Evaluate every entry of a symbolic matrix in the same real environment. -/
def evalMatrix {m n : Type*} {ι : Type*} (ρ : ι → ℝ)
    (matrix : Matrix m n (Expr ι)) : Matrix m n ℝ :=
  fun i j ↦ (matrix i j).eval ρ

/-- Symbolic multiplication of square matrices indexed by `Fin n`. -/
def mul {n : Nat} {ι : Type*}
    (left right : Matrix (Fin n) (Fin n) (Expr ι)) :
    Matrix (Fin n) (Fin n) (Expr ι) :=
  fun i j ↦ Expr.addList <|
    (List.finRange n).map fun k ↦ left i k * right k j

/-- Symbolic identity matrix indexed by `Fin n`. -/
def one {n : Nat} {ι : Type*} : Matrix (Fin n) (Fin n) (Expr ι) :=
  fun i j ↦ if i = j then .nat 1 else .nat 0

/-- Symbolic left residual `I - B A` for an approximate inverse `B` of `A`. -/
def leftResidual {n : Nat} {ι : Type*}
    (matrix proposedInverse : Matrix (Fin n) (Fin n) (Expr ι)) :
    Matrix (Fin n) (Fin n) (Expr ι) :=
  fun i j ↦ one i j - mul proposedInverse matrix i j

/-- Symbolic matrix multiplication evaluates to ordinary real matrix multiplication. -/
theorem evalMatrix_mul {n : Nat} {ι : Type*} (ρ : ι → ℝ)
    (left right : Matrix (Fin n) (Fin n) (Expr ι)) :
    evalMatrix ρ (mul left right) = evalMatrix ρ left * evalMatrix ρ right := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [evalMatrix, mul, Expr.eval_addList, List.map_map]
  rfl

/-- The symbolic identity evaluates to the ordinary identity matrix. -/
theorem evalMatrix_one {n : Nat} {ι : Type*} (ρ : ι → ℝ) :
    evalMatrix ρ (one : Matrix (Fin n) (Fin n) (Expr ι)) = 1 := by
  ext i j
  by_cases hij : i = j <;> simp [evalMatrix, one, Matrix.one_apply, hij]

/-- Symbolic left-residual formation commutes with evaluation. -/
theorem evalMatrix_leftResidual {n : Nat} {ι : Type*} (ρ : ι → ℝ)
    (matrix proposedInverse : Matrix (Fin n) (Fin n) (Expr ι)) :
    evalMatrix ρ (leftResidual matrix proposedInverse) =
      1 - evalMatrix ρ proposedInverse * evalMatrix ρ matrix := by
  rw [← evalMatrix_one ρ, ← evalMatrix_mul]
  rfl

/-! ## Executable finite matrix traversal -/

/-- Traverse a `Fin n`-indexed family through `Option`, failing at the first absent entry. -/
def traverseFin {α : Type*} : {n : Nat} → (Fin n → Option α) → Option (Fin n → α)
  | 0, _f => some Fin.elim0
  | _n + 1, f => do
      let head ← f 0
      let tail ← traverseFin fun i ↦ f i.succ
      pure (Fin.cases head tail)

/-- A successful finite traversal records the result of every input computation. -/
theorem traverseFin_apply {α : Type*} {n : Nat} {f : Fin n → Option α}
    {result : Fin n → α} (hresult : traverseFin f = some result) (i : Fin n) :
    f i = some (result i) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      simp only [traverseFin, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.some.injEq] at hresult
      obtain ⟨head, hhead, tail, htail, rfl⟩ := hresult
      exact Fin.cases hhead (fun j ↦ ih htail j) i

/-- Assemble a successful finite traversal from successful computations at every index. -/
theorem traverseFin_eq_some_of_apply {α : Type*} {n : Nat} {f : Fin n → Option α}
    {result : Fin n → α} (hresult : ∀ i, f i = some (result i)) :
    traverseFin f = some result := by
  induction n with
  | zero => exact congrArg some (funext fun i ↦ Fin.elim0 i)
  | succ n ih =>
      rw [traverseFin, hresult 0, ih fun i ↦ hresult i.succ]
      exact congrArg some (Fin.cons_self_tail result)

/-- Evaluate every entry of a finite symbolic matrix with one certified context. -/
def evalMatrix? {α : Type*} {ι : Type*} {s : Set α} {ρ : α → ι → ℝ} {n : Nat}
    (context : ExprIntervalContext RationalInterval s ρ)
    (matrix : Matrix (Fin n) (Fin n) (Expr ι)) :
    Option (Matrix (Fin n) (Fin n) RationalInterval) :=
  traverseFin fun i ↦ traverseFin fun j ↦ context.eval (matrix i j)

/-- Every entry returned by `evalMatrix?` is the result of the certified evaluator. -/
theorem evalMatrix?_apply {α : Type*} {ι : Type*} {s : Set α} {ρ : α → ι → ℝ} {n : Nat}
    (context : ExprIntervalContext RationalInterval s ρ)
    (matrix : Matrix (Fin n) (Fin n) (Expr ι))
    (intervals : Matrix (Fin n) (Fin n) RationalInterval)
    (hresult : evalMatrix? context matrix = some intervals) (i j : Fin n) :
    context.eval (matrix i j) = some (intervals i j) :=
  traverseFin_apply (traverseFin_apply hresult i) j

/-- Assemble a successful matrix evaluation from successful evaluation of every entry. -/
theorem evalMatrix?_eq_some_of_apply
    {α : Type*} {ι : Type*} {s : Set α} {ρ : α → ι → ℝ} {n : Nat}
    (context : ExprIntervalContext RationalInterval s ρ)
    (matrix : Matrix (Fin n) (Fin n) (Expr ι))
    (intervals : Matrix (Fin n) (Fin n) RationalInterval)
    (hresult : ∀ i j, context.eval (matrix i j) = some (intervals i j)) :
    evalMatrix? context matrix = some intervals :=
  traverseFin_eq_some_of_apply fun i ↦ traverseFin_eq_some_of_apply (hresult i)

/-! ## Automatic row-sum verification -/

/-- Successful interval evaluation data for a symbolic left residual. -/
abbrev ResidualIntervals (n : Nat) :=
  Matrix (Fin n) (Fin n) RationalInterval

namespace ResidualIntervals

variable {n : Nat}

/-- Exact rational absolute upper bounds extracted from every interval. -/
def entryBounds (result : ResidualIntervals n) : ResidualEntryBounds (Fin n) :=
  fun i j ↦ (result i j).absMax

/-- Exact rational absolute row sum for one row. -/
def rowSum (result : ResidualIntervals n) (i : Fin n) : ℚ :=
  ((List.finRange n).map fun j ↦ (result i j).absMax).sum

/-- Largest absolute row sum, with value zero for the empty matrix. -/
def residualBound (result : ResidualIntervals n) : ℚ :=
  ((List.finRange n).map result.rowSum).foldr max 0

/-- Every row sum is bounded by the automatically computed maximum. -/
theorem rowSum_le_residualBound (result : ResidualIntervals n) (i : Fin n) :
    result.rowSum i ≤ result.residualBound :=
  List.le_max_of_le' 0 (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩) le_rfl

/-- The automatically computed row-sum bound is nonnegative. -/
theorem residualBound_nonneg (result : ResidualIntervals n) :
    0 ≤ result.residualBound := by
  unfold residualBound
  induction (List.finRange n).map result.rowSum with
  | nil => exact le_rfl
  | cons _ _ ih => exact le_max_of_le_right ih

end ResidualIntervals

/-- Symbolic input data for approximate-inverse verification. -/
structure ApproximateInverseData (n : Nat) (ι : Type*) where
  /-- Symbolic target matrix. -/
  matrix : Matrix (Fin n) (Fin n) (Expr ι)
  /-- Symbolic proposed inverse. -/
  proposedInverse : Matrix (Fin n) (Fin n) (Expr ι)

namespace ApproximateInverseData

variable {α : Type*} {ι : Type*} {s : Set α} {ρ : α → ι → ℝ} {n : Nat}

/-- Symbolic left residual attached to approximate-inverse input data. -/
def leftResidual (data : ApproximateInverseData n ι) :
    Matrix (Fin n) (Fin n) (Expr ι) :=
  Expression.leftResidual data.matrix data.proposedInverse

/-- Evaluate the target, proposal, and automatic residual bound at one parameter point. -/
def candidateAt (data : ApproximateInverseData n ι)
    (result : ResidualIntervals n) (env : ι → ℝ) :
    ApproximateInverseCandidate (Fin n) ℝ where
  matrix := evalMatrix env data.matrix
  proposedInverse := evalMatrix env data.proposedInverse
  residualBound :=
    ⟨(result.residualBound : ℝ), by
      exact_mod_cast result.residualBound_nonneg⟩

/-- Evaluate all symbolic residual entries and retain their exact rational intervals. -/
def compileResidual? (context : ExprIntervalContext RationalInterval s ρ)
    (data : ApproximateInverseData n ι) : Option (ResidualIntervals n) := do
  let intervals ← evalMatrix? context data.leftResidual
  pure intervals

/--
Run the full automatic checker.

The strict row-sum threshold is decided over exact rationals. Failure of any entry evaluation or
failure of the threshold returns `none`.
-/
def certify? (context : ExprIntervalContext RationalInterval s ρ)
    (data : ApproximateInverseData n ι) : Option (ResidualIntervals n) := do
  let result ← data.compileResidual? context
  if result.residualBound < 1 then some result else none

/-- A successful residual compilation encloses every symbolic residual entry. -/
theorem compileResidual?_abs_le
    (context : ExprIntervalContext RationalInterval s ρ)
    (data : ApproximateInverseData n ι) (result : ResidualIntervals n)
    (hresult : data.compileResidual? context = some result)
    (x : α) (hx : x ∈ s) (i j : Fin n) :
    |(data.leftResidual i j).eval (ρ x)| ≤
      (result.entryBounds i j : ℝ) :=
  RationalInterval.abs_le_absMax <|
    context.sound (evalMatrix?_apply context data.leftResidual result hresult i j) x hx

/-- A successful full check has exact rational row-sum bound strictly below one. -/
theorem residualBound_lt_one_of_certify?_eq_some
    (context : ExprIntervalContext RationalInterval s ρ)
    (data : ApproximateInverseData n ι) (result : ResidualIntervals n)
    (hresult : data.certify? context = some result) :
    result.residualBound < 1 := by
  simp only [certify?, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.ite_none_right_eq_some, Option.some.injEq] at hresult
  obtain ⟨_, _, h, rfl⟩ := hresult
  exact h

/-- A successful full check includes successful interval compilation of the same result. -/
theorem compileResidual?_eq_some_of_certify?_eq_some
    (context : ExprIntervalContext RationalInterval s ρ)
    (data : ApproximateInverseData n ι) (result : ResidualIntervals n)
    (hresult : data.certify? context = some result) :
    data.compileResidual? context = some result := by
  simp only [certify?, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.ite_none_right_eq_some, Option.some.injEq] at hresult
  obtain ⟨_, h, -, rfl⟩ := hresult
  exact h

/-- A successful expression check certifies the row-sum obligations at every domain point. -/
theorem entryBounds_isCertifiedAt
    (context : ExprIntervalContext RationalInterval s ρ)
    (data : ApproximateInverseData n ι) (result : ResidualIntervals n)
    (hresult : data.certify? context = some result)
    (x : α) (hx : x ∈ s) :
    result.entryBounds.IsCertified (data.candidateAt result (ρ x)) := by
  refine ⟨fun i j ↦ ?_, fun i ↦ ?_, ?_⟩
  · change ‖(1 - evalMatrix (ρ x) data.proposedInverse * evalMatrix (ρ x) data.matrix) i j‖ ≤
      (result.entryBounds i j : ℝ)
    rw [← evalMatrix_leftResidual]
    exact data.compileResidual?_abs_le context result
      (data.compileResidual?_eq_some_of_certify?_eq_some context result hresult) x hx i j
  · change (result.rowSum i : ℝ) ≤ (result.residualBound : ℝ)
    exact_mod_cast result.rowSum_le_residualBound i
  · change (result.residualBound : ℝ) < 1
    exact_mod_cast data.residualBound_lt_one_of_certify?_eq_some context result hresult

/-- Every matrix accepted by the expression checker is invertible throughout the domain. -/
theorem matrix_isUnitAt
    (context : ExprIntervalContext RationalInterval s ρ)
    (data : ApproximateInverseData n ι) (result : ResidualIntervals n)
    (hresult : data.certify? context = some result)
    (x : α) (hx : x ∈ s) :
    IsUnit (evalMatrix (ρ x) data.matrix) :=
  result.entryBounds.matrix_isUnit (data.candidateAt result (ρ x))
    (data.entryBounds_isCertifiedAt context result hresult x hx)

end ApproximateInverseData

end

end Expression

end CAS.Continuum.MatrixVerification
