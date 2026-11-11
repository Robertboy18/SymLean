/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Interval.Rational.Arithmetic

/-!
# Affine arithmetic with interval remainders

An affine form `x₀ + ∑ i, xᵢ εᵢ` has an exact rational center and rational coefficients indexed
by a finite type of noise symbols `εᵢ`. An `AffineModel` adds a rational interval for the
nonlinear remainder: it represents `x` at a noise assignment `ε` when `x - affine.eval ε` lies in
the remainder. Each affine term is enclosed with `RationalInterval.mul`, and the terms are
combined by exact endpoint sums. Multiplication keeps the constant and linear terms, bounds the
diagonal quadratic terms with `εᵢ ^ 2 ∈ [0, 1]` and the off-diagonal ones with
`εᵢ * εⱼ ∈ [-1, 1]`, and propagates the remainders of the factors by interval arithmetic. All
arithmetic is exact rational, with a fixed finite set of noise symbols.

## Main definitions

* `AffineForm`, `AffineForm.eval`, `AffineForm.rangeOn`, `AffineForm.mulRangeOn`: affine forms,
  their values, and enclosures of a form and of a product of two forms over a rational box.
* `AffineModel`, `AffineModel.Represents`, `AffineModel.mul`, `AffineModel.pow`,
  `AffineModel.range`: affine models, their semantics, multiplication, powers by binary
  exponentiation, and the enclosure on the unit noise box.

## Main results

* `AffineForm.mem_rangeOn`, `AffineForm.mul_mem_mulRangeOn`: the box enclosures contain every
  value of a form and every product of values of two forms.
* `AffineModel.Represents.add`, `Represents.sub`, `Represents.mul`, `Represents.pow`: the model
  operations preserve `Represents`, multiplication and powers when `|εᵢ| ≤ 1` for all `i`.
* `AffineModel.mem_range`: every value represented at a point of the unit noise box lies in
  `range`.

## Implementation notes

Affine forms, their range `x₀ ± ∑ i, |xᵢ|` on the unit box and the affine part `linearMul` of a
product are classical (Andrade, Comba and Stolfi; de Figueiredo and Stolfi). Both papers replace
the rest of a product by a new noise symbol whose coefficient bounds it, at simplest
`(∑ i, |xᵢ|) * (∑ i, |yᵢ|)`, and add rounding errors to such coefficients. We keep an interval
remainder instead, so the noise type `ι` stays fixed and an `AffineModel` is a first-order
Taylor model in the noise symbols, a method de Figueiredo and Stolfi name among the closest to
theirs. On the unit box `mulRemainderOn` is the symmetric interval with that simplest radius.
The pairwise bound `quadraticRange` of `AffineModel.mul` is ours and lies inside that interval.
Exact rational arithmetic leaves no rounding errors. The soundness theorems hold for every noise
assignment in the box, so a concrete enclosure needs only the evaluation of its rational
endpoints.

## References

* Marcus Vinicius Alvim Andrade, João Luiz Dihl Comba and Jorge Stolfi, "Affine Arithmetic",
  Interval'94, St. Petersburg, Russia, March 1994; authors' draft at
  <https://graphics.stanford.edu/~comba/papers/aa-93-12-petersburg-paper.pdf>. Section 3 for
  affine forms and noise symbols, Section 4.3 for their product.
* Luiz Henrique de Figueiredo and Jorge Stolfi, "Affine Arithmetic: Concepts and Applications",
  *Numerical Algorithms* 37 (2004), pp. 147-158,
  <https://doi.org/10.1023/B:NUMA.0000049462.70970.b6>; preprint at
  <https://lhf.impa.br/ftp/papers/aa.ps.gz>. In the preprint, Section 3 for affine forms and their
  range, Section 3.4 for the product and its simplest error bound.
-/

@[expose] public section

namespace CAS.Continuum

/-- An affine form with exact rational center and coefficients. -/
structure AffineForm (ι : Type*) where
  /-- Constant part of the affine form. -/
  center : ℚ
  /-- Coefficients indexed by noise symbols. -/
  coefficients : ι → ℚ

namespace AffineForm

variable {ι : Type*}

/-- The constant affine form with value `q`. -/
def const (q : ℚ) : AffineForm ι :=
  ⟨q, fun _ ↦ 0⟩

/-- The affine form representing one noise symbol. -/
def noise [DecidableEq ι] (i : ι) : AffineForm ι :=
  ⟨0, fun j ↦ if i = j then 1 else 0⟩

/-- Evaluate an affine form at a real assignment of its noise symbols. -/
def eval [Fintype ι] (a : AffineForm ι) (ε : ι → ℝ) : ℝ :=
  (a.center : ℝ) + ∑ i, (a.coefficients i : ℝ) * ε i

/-- Add two affine forms coefficientwise. -/
def add (a b : AffineForm ι) : AffineForm ι :=
  ⟨a.center + b.center, fun i ↦ a.coefficients i + b.coefficients i⟩

/-- Negate an affine form coefficientwise. -/
def neg (a : AffineForm ι) : AffineForm ι :=
  ⟨-a.center, fun i ↦ -a.coefficients i⟩

/-- Subtract two affine forms coefficientwise. -/
def sub (a b : AffineForm ι) : AffineForm ι :=
  add a b.neg

/-- Multiply the center and every coefficient by an exact rational scalar. -/
def scale (q : ℚ) (a : AffineForm ι) : AffineForm ι :=
  ⟨q * a.center, fun i ↦ q * a.coefficients i⟩

/-- Remove the center while retaining every noise coefficient. -/
def deviation (a : AffineForm ι) : AffineForm ι :=
  ⟨0, a.coefficients⟩

/-- The affine part of a product, before enclosing its quadratic remainder. -/
def linearMul (a b : AffineForm ι) : AffineForm ι :=
  ⟨a.center * b.center,
    fun i ↦ a.center * b.coefficients i + b.center * a.coefficients i⟩

/-- A constant form evaluates to its center at every noise assignment. -/
@[simp] theorem eval_const [Fintype ι] (q : ℚ) (ε : ι → ℝ) :
    (const q).eval ε = q := by
  simp [const, eval]

/-- The noise form `noise i` evaluates to the `i`-th noise value. -/
@[simp] theorem eval_noise [Fintype ι] [DecidableEq ι] (i : ι) (ε : ι → ℝ) :
    (noise i).eval ε = ε i := by
  simp [noise, eval, apply_ite (Rat.cast : ℚ → ℝ), ite_mul]

/-- Evaluation of affine forms is additive. -/
@[simp] theorem eval_add [Fintype ι] (a b : AffineForm ι) (ε : ι → ℝ) :
    (a.add b).eval ε = a.eval ε + b.eval ε := by
  simp only [add, eval, Rat.cast_add, add_mul, Finset.sum_add_distrib]
  ring

/-- Evaluation commutes with negation. -/
@[simp] theorem eval_neg [Fintype ι] (a : AffineForm ι) (ε : ι → ℝ) :
    a.neg.eval ε = -a.eval ε := by
  simp only [neg, eval, Rat.cast_neg, neg_mul, Finset.sum_neg_distrib]
  ring

/-- Evaluation commutes with subtraction. -/
@[simp] theorem eval_sub [Fintype ι] (a b : AffineForm ι) (ε : ι → ℝ) :
    (a.sub b).eval ε = a.eval ε - b.eval ε := by
  simp [sub, sub_eq_add_neg]

/-- Scaling by a rational `q` multiplies the value by `q`. -/
@[simp] theorem eval_scale [Fintype ι] (q : ℚ) (a : AffineForm ι) (ε : ι → ℝ) :
    (a.scale q).eval ε = (q : ℝ) * a.eval ε := by
  simp only [scale, eval, Rat.cast_mul, mul_assoc, ← Finset.mul_sum]
  ring

/-- The deviation of a form is its value minus its center. -/
@[simp] theorem eval_deviation [Fintype ι] (a : AffineForm ι) (ε : ι → ℝ) :
    a.deviation.eval ε = a.eval ε - a.center := by
  simp [deviation, eval]

/-- Value of the affine part of a product. Writing `a = a₀ + A`, `b = b₀ + B` with centers
`a₀, b₀` and deviations `A, B`, the full product is `a₀b₀ + a₀B + b₀A + AB`; `linearMul` keeps
the first three terms, and this lemma expresses their sum as `a₀·b + b₀·a - a₀b₀`. The dropped
term `AB` is what `mulRemainderOn` encloses. -/
@[simp] theorem eval_linearMul [Fintype ι]
    (a b : AffineForm ι) (ε : ι → ℝ) :
    (a.linearMul b).eval ε =
      (a.center : ℝ) * b.eval ε + (b.center : ℝ) * a.eval ε -
        (a.center : ℝ) * b.center := by
  simp only [linearMul, eval, Rat.cast_mul, Rat.cast_add, add_mul,
    Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  ring

/-! ## Rational-box enclosures -/

/-- Interval enclosure of one rational coefficient times one boxed noise symbol. -/
def termRange (q : ℚ) (I : RationalInterval) : RationalInterval :=
  (RationalInterval.const q).mul I

/--
Enclose an affine form over a rational box of noise-symbol values.

Each scalar product is enclosed by `RationalInterval.mul`.
-/
def rangeOn [Fintype ι] (a : AffineForm ι)
    (box : ι → RationalInterval) : RationalInterval where
  lo := a.center + ∑ i, (termRange (a.coefficients i) (box i)).lo
  hi := a.center + ∑ i, (termRange (a.coefficients i) (box i)).hi
  hle := add_le_add le_rfl
    (Finset.sum_le_sum fun i _ ↦ (termRange (a.coefficients i) (box i)).hle)

/-- A real noise assignment belongs to a rational box pointwise. -/
def MemBox (box : ι → RationalInterval) (ε : ι → ℝ) : Prop :=
  ∀ i, (box i).MemReal (ε i)

private theorem sum_termRange_lower_le [Fintype ι] (a : AffineForm ι)
    (box : ι → RationalInterval) {ε : ι → ℝ} (hε : MemBox box ε) :
    ((∑ i, (termRange (a.coefficients i) (box i)).lo : ℚ) : ℝ) ≤
      ∑ i, (a.coefficients i : ℝ) * ε i := by
  push_cast
  exact Finset.sum_le_sum fun i _ ↦
    (RationalInterval.mul_sound (RationalInterval.memReal_const _) (hε i)).1

private theorem sum_termRange_le_upper [Fintype ι] (a : AffineForm ι)
    (box : ι → RationalInterval) {ε : ι → ℝ} (hε : MemBox box ε) :
    (∑ i, (a.coefficients i : ℝ) * ε i) ≤
      ((∑ i, (termRange (a.coefficients i) (box i)).hi : ℚ) : ℝ) := by
  push_cast
  exact Finset.sum_le_sum fun i _ ↦
    (RationalInterval.mul_sound (RationalInterval.memReal_const _) (hε i)).2

/-- `rangeOn` contains every evaluation whose noise assignment belongs to the box. -/
theorem mem_rangeOn [Fintype ι] (a : AffineForm ι)
    (box : ι → RationalInterval) {ε : ι → ℝ} (hε : MemBox box ε) :
    (a.rangeOn box).MemReal (a.eval ε) := by
  constructor
  · simpa [rangeOn, eval, RationalInterval.MemReal] using
      add_le_add_left (sum_termRange_lower_le a box hε) (a.center : ℝ)
  · simpa [rangeOn, eval, RationalInterval.MemReal] using
      add_le_add_left (sum_termRange_le_upper a box hε) (a.center : ℝ)

/-! ## Multiplication with an interval remainder -/

/--
Checked interval remainder for affine multiplication over a rational box.

After retaining the constant and first-order terms in `linearMul`, the omitted term is exactly the
product of the two deviations, which `RationalInterval.mul` encloses.
-/
def mulRemainderOn [Fintype ι] (a b : AffineForm ι)
    (box : ι → RationalInterval) : RationalInterval :=
  (a.deviation.rangeOn box).mul (b.deviation.rangeOn box)

/-- The affine linear part plus the checked interval remainder encloses a product. -/
def mulRangeOn [Fintype ι] (a b : AffineForm ι)
    (box : ι → RationalInterval) : RationalInterval :=
  (a.linearMul b).rangeOn box |>.add (a.mulRemainderOn b box)

/-- The error in the affine product is exactly the product of the two deviations. -/
theorem mul_sub_eval_linearMul [Fintype ι]
    (a b : AffineForm ι) (ε : ι → ℝ) :
    a.eval ε * b.eval ε - (a.linearMul b).eval ε =
      a.deviation.eval ε * b.deviation.eval ε := by
  rw [eval_linearMul, eval_deviation, eval_deviation]
  ring

/-- The interval remainder contains the exact error of the affine product. -/
theorem mul_sub_eval_linearMul_mem_mulRemainderOn [Fintype ι]
    (a b : AffineForm ι) (box : ι → RationalInterval)
    {ε : ι → ℝ} (hε : MemBox box ε) :
    (a.mulRemainderOn b box).MemReal
      (a.eval ε * b.eval ε - (a.linearMul b).eval ε) := by
  rw [mul_sub_eval_linearMul]
  exact RationalInterval.mul_sound
    (mem_rangeOn a.deviation box hε) (mem_rangeOn b.deviation box hε)

/-- `mulRangeOn` soundly encloses the pointwise product over a rational box. -/
theorem mul_mem_mulRangeOn [Fintype ι]
    (a b : AffineForm ι) (box : ι → RationalInterval)
    {ε : ι → ℝ} (hε : MemBox box ε) :
    (a.mulRangeOn b box).MemReal (a.eval ε * b.eval ε) := by
  have := RationalInterval.add_sound
    (mem_rangeOn (a.linearMul b) box hε) (mul_sub_eval_linearMul_mem_mulRemainderOn a b box hε)
  rwa [add_sub_cancel] at this

/-! ## Unit-noise boxes -/

/-- The standard affine-arithmetic noise box `[-1, 1]` in every coordinate. -/
def unitBox (_ : ι) : RationalInterval :=
  RationalInterval.negOneOne

/-- A noise assignment lies in the standard unit box exactly when every value lies in `[-1, 1]`. -/
theorem mem_unitBox_iff (ε : ι → ℝ) :
    MemBox (unitBox : ι → RationalInterval) ε ↔ ∀ i, |ε i| ≤ 1 := by
  simp [MemBox, unitBox, RationalInterval.negOneOne, RationalInterval.MemReal, abs_le]

/-- Enclose an affine form when every noise symbol ranges over `[-1, 1]`. -/
def range [Fintype ι] (a : AffineForm ι) : RationalInterval :=
  a.rangeOn unitBox

/-- The unit-noise range contains every evaluation with noise magnitudes at most one. -/
theorem mem_range [Fintype ι] (a : AffineForm ι) {ε : ι → ℝ}
    (hε : ∀ i, |ε i| ≤ 1) :
    a.range.MemReal (a.eval ε) :=
  mem_rangeOn a unitBox ((mem_unitBox_iff ε).2 hε)

/-- Enclose a product when every noise symbol ranges over `[-1, 1]`. -/
def mulRange [Fintype ι] (a b : AffineForm ι) : RationalInterval :=
  a.mulRangeOn b unitBox

/-- The unit-noise multiplication range contains every corresponding product. -/
theorem mul_mem_mulRange [Fintype ι]
    (a b : AffineForm ι) {ε : ι → ℝ} (hε : ∀ i, |ε i| ≤ 1) :
    (a.mulRange b).MemReal (a.eval ε * b.eval ε) :=
  mul_mem_mulRangeOn a b unitBox ((mem_unitBox_iff ε).2 hε)

end AffineForm

/-! ## Affine models -/

/--
An affine approximation together with a checked interval for its additive remainder.

The model represents a value `x` at a noise assignment `ε` when
`x - affine.eval ε ∈ remainder`. The remainder is a `RationalInterval`,
so the affine kernel uses the ordinary interval semantics.
-/
structure AffineModel (ι : Type*) where
  /-- The dependency-preserving constant and linear part. -/
  affine : AffineForm ι
  /-- A checked enclosure of every term not retained in `affine`. -/
  remainder : RationalInterval

namespace AffineModel

variable {ι : Type*}

/-- The exact constant model. -/
def const (q : ℚ) : AffineModel ι :=
  ⟨.const q, RationalInterval.const 0⟩

/-- Regard an affine form as a model with zero remainder. -/
def ofAffine (a : AffineForm ι) : AffineModel ι :=
  ⟨a, RationalInterval.const 0⟩

/-- A model represents a real value when its affine residual lies in the remainder interval. -/
def Represents [Fintype ι] (m : AffineModel ι) (ε : ι → ℝ) (x : ℝ) : Prop :=
  m.remainder.MemReal (x - m.affine.eval ε)

/-- Add affine models and their checked remainders. -/
def add (a b : AffineModel ι) : AffineModel ι :=
  ⟨a.affine.add b.affine, a.remainder.add b.remainder⟩

/-- Negate both parts of an affine model. -/
def neg (a : AffineModel ι) : AffineModel ι :=
  ⟨a.affine.neg, a.remainder.neg⟩

/-- Subtract two affine models. -/
def sub (a b : AffineModel ι) : AffineModel ι :=
  a.add b.neg

/-- The exact rational interval `[0, 1]` used for a squared unit noise. -/
def unitSquareRange : RationalInterval :=
  RationalInterval.ofBounds 0 1 (by norm_num)

/--
Range of one coefficient times either a squared noise (`i = j`) or a product of distinct noises.
-/
def quadraticTermRange [DecidableEq ι]
    (a b : AffineForm ι) (i j : ι) : RationalInterval :=
  (RationalInterval.const (a.coefficients i * b.coefficients j)).mul
    (if i = j then unitSquareRange else RationalInterval.negOneOne)

/--
Checked enclosure of the quadratic term obtained by multiplying the deviations of two affine
forms on the unit-noise box.

Diagonal terms retain the fact that a noise square is nonnegative. Off-diagonal terms use the
standard `[-1, 1]` product bound. Summing ordered pairs is exact and avoids imposing an arbitrary
ordering on the noise type.
-/
def quadraticRange [Fintype ι] [DecidableEq ι]
    (a b : AffineForm ι) : RationalInterval where
  lo := ∑ i, ∑ j, (quadraticTermRange a b i j).lo
  hi := ∑ i, ∑ j, (quadraticTermRange a b i j).hi
  hle := Finset.sum_le_sum fun i _ ↦
    Finset.sum_le_sum fun j _ ↦ (quadraticTermRange a b i j).hle

/--
Multiply two affine models.

For represented values `x = A + r` and `y = B + s`, the affine part of the product is the
constant-linear part of `A * B`. Its remainder encloses the quadratic deviation product,
`A * s`, `B * r`, and `r * s`, in that order.
-/
def mul [Fintype ι] [DecidableEq ι]
    (a b : AffineModel ι) : AffineModel ι :=
  ⟨a.affine.linearMul b.affine,
    (((quadraticRange a.affine b.affine).add
      (a.affine.range.mul b.remainder)).add
      (b.affine.range.mul a.remainder)).add
      (a.remainder.mul b.remainder)⟩

/-- One binary-exponentiation step for `pow`.

Given `accumulator`, the model of `a ^ n`, this returns the model of `a ^ (2 * n + 1)` when
`odd` is `true` and of `a ^ (2 * n)` otherwise. When `odd` is `false` and `n = 0` the
accumulator is returned unchanged, the base-case equation that `Nat.binaryRec_eq` needs. -/
def powStep [Fintype ι] [DecidableEq ι]
    (a : AffineModel ι) (odd : Bool) (n : Nat)
    (accumulator : AffineModel ι) : AffineModel ι :=
  if odd then
    (accumulator.mul accumulator).mul a
  else if n = 0 then
    accumulator
  else
    accumulator.mul accumulator

/-- Raise an affine model to a natural power by binary exponentiation. -/
def pow [Fintype ι] [DecidableEq ι]
    (a : AffineModel ι) (n : Nat) : AffineModel ι :=
  Nat.binaryRec (const 1) (powStep a) n

private theorem pow_bit [Fintype ι] [DecidableEq ι]
    (a : AffineModel ι) (odd : Bool) (n : Nat) :
    a.pow (Nat.bit odd n) = powStep a odd n (a.pow n) := by
  rw [AffineModel.pow, Nat.binaryRec_eq odd n (Or.inl rfl)]
  rfl

/-- The range obtained by adding the affine range and checked remainder. -/
def range [Fintype ι] (m : AffineModel ι) : RationalInterval :=
  m.affine.range.add m.remainder

/-- The constant model represents its own value, with zero remainder. -/
@[simp] theorem represents_const [Fintype ι] (q : ℚ) (ε : ι → ℝ) :
    (const q).Represents ε q := by
  simpa [Represents, const] using RationalInterval.memReal_const (0 : ℚ)

/-- An affine form regarded as a model represents exactly its evaluation. -/
@[simp] theorem represents_ofAffine [Fintype ι]
    (a : AffineForm ι) (ε : ι → ℝ) :
    (ofAffine a).Represents ε (a.eval ε) := by
  simpa [Represents, ofAffine] using RationalInterval.memReal_const (0 : ℚ)

/-- Addition preserves the model semantics. -/
theorem Represents.add [Fintype ι] {a b : AffineModel ι} {ε : ι → ℝ} {x y : ℝ}
    (hx : a.Represents ε x) (hy : b.Represents ε y) :
    (a.add b).Represents ε (x + y) := by
  change (a.remainder.add b.remainder).MemReal
    (x + y - (a.affine.add b.affine).eval ε)
  convert RationalInterval.add_sound hx hy using 1
  simp only [AffineForm.eval_add]
  ring

/-- Negation preserves the model semantics. -/
theorem Represents.neg [Fintype ι] {a : AffineModel ι} {ε : ι → ℝ} {x : ℝ}
    (hx : a.Represents ε x) : a.neg.Represents ε (-x) := by
  change a.remainder.neg.MemReal (-x - a.affine.neg.eval ε)
  convert RationalInterval.neg_sound hx using 1
  simp only [AffineForm.eval_neg]
  ring

/-- Subtraction preserves the model semantics. -/
theorem Represents.sub [Fintype ι] {a b : AffineModel ι} {ε : ι → ℝ} {x y : ℝ}
    (hx : a.Represents ε x) (hy : b.Represents ε y) :
    (a.sub b).Represents ε (x - y) := by
  change (a.add b.neg).Represents ε (x - y)
  simpa only [sub_eq_add_neg] using hx.add hy.neg

/-- The square of a unit noise lies in `[0,1]`. -/
theorem square_mem_unitSquareRange {x : ℝ} (hx : |x| ≤ 1) :
    unitSquareRange.MemReal (x * x) := by
  simpa [unitSquareRange, RationalInterval.MemReal, RationalInterval.ofBounds] using
    And.intro (mul_self_nonneg x) (by nlinarith [abs_le.mp hx] : x * x ≤ 1)

private theorem mul_mem_negOneOne {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    RationalInterval.negOneOne.MemReal (x * y) := by
  have habs : |x * y| ≤ 1 := by
    simpa [abs_mul] using mul_le_mul hx hy (abs_nonneg y) zero_le_one
  simpa [RationalInterval.negOneOne, RationalInterval.MemReal] using abs_le.mp habs

private theorem mem_quadraticTermRange [DecidableEq ι]
    (a b : AffineForm ι) {ε : ι → ℝ} (hε : ∀ i, |ε i| ≤ 1) (i j : ι) :
    (quadraticTermRange a b i j).MemReal
      ((a.coefficients i : ℝ) * ε i * ((b.coefficients j : ℝ) * ε j)) := by
  have hcoefficient :=
    RationalInterval.memReal_const (a.coefficients i * b.coefficients j)
  rw [show (a.coefficients i : ℝ) * ε i * ((b.coefficients j : ℝ) * ε j) =
    ((a.coefficients i * b.coefficients j : ℚ) : ℝ) * (ε i * ε j) by push_cast; ring]
  unfold quadraticTermRange
  split_ifs with hij
  · subst hij
    exact RationalInterval.mul_sound hcoefficient (square_mem_unitSquareRange (hε i))
  · exact RationalInterval.mul_sound hcoefficient (mul_mem_negOneOne (hε i) (hε j))

private theorem sum_quadraticTermRange_lower_le [Fintype ι] [DecidableEq ι]
    (a b : AffineForm ι) {ε : ι → ℝ} (hε : ∀ i, |ε i| ≤ 1) :
    ((∑ i, ∑ j, (quadraticTermRange a b i j).lo : ℚ) : ℝ) ≤
      ∑ i, ∑ j, (a.coefficients i : ℝ) * ε i *
        ((b.coefficients j : ℝ) * ε j) := by
  push_cast
  exact Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦
    (mem_quadraticTermRange a b hε i j).1

private theorem sum_quadraticTermRange_le_upper [Fintype ι] [DecidableEq ι]
    (a b : AffineForm ι) {ε : ι → ℝ} (hε : ∀ i, |ε i| ≤ 1) :
    (∑ i, ∑ j, (a.coefficients i : ℝ) * ε i *
        ((b.coefficients j : ℝ) * ε j)) ≤
      ((∑ i, ∑ j, (quadraticTermRange a b i j).hi : ℚ) : ℝ) := by
  push_cast
  exact Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦
    (mem_quadraticTermRange a b hε i j).2

/-- The quadratic range contains the exact product of affine deviations. -/
theorem deviation_mul_deviation_mem_quadraticRange [Fintype ι] [DecidableEq ι]
    (a b : AffineForm ι) {ε : ι → ℝ} (hε : ∀ i, |ε i| ≤ 1) :
    (quadraticRange a b).MemReal (a.deviation.eval ε * b.deviation.eval ε) := by
  have h (c : AffineForm ι) : c.deviation.eval ε = ∑ i, (c.coefficients i : ℝ) * ε i := by
    simp [AffineForm.deviation, AffineForm.eval]
  rw [h, h, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  constructor
  · simpa [quadraticRange, mul_assoc] using sum_quadraticTermRange_lower_le a b hε
  · simpa [quadraticRange, mul_assoc] using sum_quadraticTermRange_le_upper a b hε

/-- Multiplication preserves the model semantics on the unit-noise box. -/
theorem Represents.mul [Fintype ι] [DecidableEq ι]
    {a b : AffineModel ι} {ε : ι → ℝ} {x y : ℝ}
    (hx : a.Represents ε x) (hy : b.Represents ε y)
    (hε : ∀ i, |ε i| ≤ 1) :
    (a.mul b).Represents ε (x * y) := by
  have hsum := RationalInterval.add_sound (RationalInterval.add_sound
    (RationalInterval.add_sound (deviation_mul_deviation_mem_quadraticRange a.affine b.affine hε)
      (RationalInterval.mul_sound (AffineForm.mem_range a.affine hε) hy))
    (RationalInterval.mul_sound (AffineForm.mem_range b.affine hε) hx))
    (RationalInterval.mul_sound hx hy)
  change ((((quadraticRange a.affine b.affine).add (a.affine.range.mul b.remainder)).add
    (b.affine.range.mul a.remainder)).add (a.remainder.mul b.remainder)).MemReal
      (x * y - (a.affine.linearMul b.affine).eval ε)
  convert hsum using 1
  rw [← AffineForm.mul_sub_eval_linearMul]
  ring

/-- Natural powers preserve the model semantics on the unit-noise box. -/
theorem Represents.pow [Fintype ι] [DecidableEq ι]
    {a : AffineModel ι} {ε : ι → ℝ} {x : ℝ}
    (hx : a.Represents ε x) (n : Nat) (hε : ∀ i, |ε i| ≤ 1) :
    (a.pow n).Represents ε (x ^ n) := by
  induction n using Nat.binaryRec with
  | zero => simpa [AffineModel.pow] using represents_const (ι := ι) 1 ε
  | bit odd n ih =>
      rw [pow_bit]
      cases odd with
      | false =>
        by_cases hn : n = 0
        · subst n
          simpa [powStep] using ih
        · simpa [powStep, hn, Nat.bit_false, two_mul, pow_add] using ih.mul ih hε
      | true =>
        simpa [powStep, Nat.bit_true, two_mul, pow_add, pow_succ, mul_assoc] using
          (ih.mul ih hε).mul hx hε

/-- Every represented value lies in the model's reported range. -/
theorem mem_range [Fintype ι] {m : AffineModel ι} {ε : ι → ℝ} {x : ℝ}
    (hx : m.Represents ε x) (hε : ∀ i, |ε i| ≤ 1) :
    m.range.MemReal x := by
  change (m.affine.range.add m.remainder).MemReal x
  convert RationalInterval.add_sound (AffineForm.mem_range m.affine hε) hx using 1
  ring

end AffineModel
end CAS.Continuum
