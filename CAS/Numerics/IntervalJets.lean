/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Interval.Elementary.Exp
public import CAS.Continuum.Interval.Rational.FiniteSum
public import CAS.Continuum.Interval.Rational.Arithmetic
public import CAS.Continuum.Interval.Rational.RelativeHull

/-!
# Taylor jets with rational interval coefficients

A jet of order `n` of `f` on an interval `X` is a list of rational intervals `Jₖ`, `k ≤ n`, with
`f^(k)(x) / k! ∈ Jₖ` for every `x ∈ X` (`JetEncloses`). Jets of sums, products, reciprocals and
exponentials are computed from the jets of the arguments by the recurrences of Taylor arithmetic:

* `(f g)ₖ = ∑ⱼ fⱼ g_{k-j}` (the Leibniz rule);
* `(1/f)₀ = 1/f₀`, `(1/f)ₖ = -(∑_{j ≥ 1} fⱼ (1/f)_{k-j}) / f₀` (from `f (1/f) = 1`);
* `(e^f)₀ = e^{f₀}`, `(k+1) (e^f)_{k+1} = ∑ⱼ (j+1) f_{j+1} (e^f)_{k-j}` (from `(e^f)' = f' e^f`).

With a point interval `X = {x}` the jets are the Taylor coefficients at `x` up to the outward
rounding of each coefficient and the exponential enclosures; with a whole cell they bound the
derivatives on the cell, which is what a Lagrange remainder needs.

## Main definitions

* `JetEncloses`: `f` is `C^n` on `X` and `f^(k)(x) / k! ∈ J[k]` for `k ≤ n` and `x ∈ X`.
* `IntervalJet.mul`: the jet of a product, by Cauchy sums.
* `IntervalJet.inv`: the jet of `1 / f`, when the constant coefficient does not contain zero.
* `IntervalJet.exp`: the jet of `exp ∘ f`.

## Main results

* `IntervalJet.iteratedDeriv_mul_div_factorial`: the Leibniz rule for Taylor coefficients.
* `JetEncloses.add`: the coefficientwise sum of jets of `f` and `g` is a jet of `f + g`.
* `JetEncloses.mul`: the Cauchy product of jets of `f` and `g` is a jet of `f g`.
* `JetEncloses.scaleArg`: `IntervalJet.scaleArg n c I` is a jet of `x ↦ f (c x)`.
* `JetEncloses.inv`: a successful `IntervalJet.inv n F` is a jet of `1 / f`.
* `JetEncloses.exp`: `IntervalJet.exp n order F` is a jet of `exp ∘ f`.

## Implementation notes

We evaluate the recurrences in exact rational interval arithmetic and round every coefficient
outward to `IntervalJet.roundBits` significant bits (`RationalInterval.relativeHull`), which
bounds the size of the rationals along the recurrences. The soundness proofs derive the same
recurrences for the Taylor coefficients of the real functions at each point of `X`
(`IntervalJet.iteratedDeriv_mul_div_factorial`, `iteratedDeriv_inv_div_factorial`,
`iteratedDeriv_exp_div_factorial`), and the interval operations enclose each step.

## References

* Siegfried M. Rump, "Verification methods: Rigorous results using floating-point arithmetic",
  *Acta Numerica* 19 (2010), pp. 287-449, <https://doi.org/10.1017/S096249291000005X>.
  Section 11.4, (11.8): the Taylor coefficients of products, quotients and exponentials, and
  their inclusions over an interval.
-/

@[expose] public section

namespace CAS.Numerics

open CAS.Continuum Set Finset

/-- `J` is a jet of order `n` of `f` on `X`: `f` is `C^n` at every point of `X` and
`f^(k)(x) / k! ∈ J[k]` for `k ≤ n`. -/
def JetEncloses (n : ℕ) (J : Array RationalInterval) (f : ℝ → ℝ) (X : RationalInterval) : Prop :=
  ∀ x, X.MemReal x → ContDiffAt ℝ n f x ∧
    ∀ k ≤ n, (J.getD k (RationalInterval.const 0)).MemReal (iteratedDeriv k f x / k.factorial)

namespace IntervalJet

/-- The relative precision, in bits, to which every coefficient is rounded outward. -/
def roundBits : ℕ := 192

/-- Outward rounding of a coefficient to `roundBits` relative bits. -/
def round (I : RationalInterval) : RationalInterval := RationalInterval.relativeHull roundBits I

/-- The coefficient `k` of a jet. -/
def get (J : Array RationalInterval) (k : ℕ) : RationalInterval :=
  J.getD k (RationalInterval.const 0)

/-- The jet of the constant `c`. -/
def const (n : ℕ) (c : ℚ) : Array RationalInterval :=
  Array.ofFn fun k : Fin (n + 1) ↦ RationalInterval.const (if k.val = 0 then c else 0)

/-- The jet of the identity on `X`. -/
def id (n : ℕ) (X : RationalInterval) : Array RationalInterval :=
  Array.ofFn fun k : Fin (n + 1) ↦
    if k.val = 0 then X else RationalInterval.const (if k.val = 1 then 1 else 0)

/-- The jet of a sum. -/
def add (n : ℕ) (I J : Array RationalInterval) : Array RationalInterval :=
  Array.ofFn fun k : Fin (n + 1) ↦ round ((get I k).add (get J k))

/-- The jet of a difference. -/
def sub (n : ℕ) (I J : Array RationalInterval) : Array RationalInterval :=
  Array.ofFn fun k : Fin (n + 1) ↦ round ((get I k).sub (get J k))

/-- The jet of a constant multiple. -/
def smul (n : ℕ) (c : ℚ) (I : Array RationalInterval) : Array RationalInterval :=
  Array.ofFn fun k : Fin (n + 1) ↦ round ((RationalInterval.const c).mul (get I k))

/-- The Cauchy sum `I₀ J_k + ... + I_k J₀`. -/
def cauchy (I J : Array RationalInterval) (k : ℕ) : RationalInterval :=
  RationalInterval.sum (range (k + 1)) fun j ↦ (get I j).mul (get J (k - j))

/-- The jet of a product. -/
def mul (n : ℕ) (I J : Array RationalInterval) : Array RationalInterval :=
  Array.ofFn fun k : Fin (n + 1) ↦ round (cauchy I J k)

/-- The jet of `x ↦ f(c x)` at `x` from the jet of `f` at `c x`. -/
def scaleArg (n : ℕ) (c : ℚ) (I : Array RationalInterval) : Array RationalInterval :=
  Array.ofFn fun k : Fin (n + 1) ↦ round ((RationalInterval.const (c ^ k.val)).mul (get I k))

/-- Division of an interval by an interval not containing zero. -/
def divNonzero (I J : RationalInterval) : Option RationalInterval :=
  if h : 0 < J.lo then some (I.divPositive J h)
  else if h' : 0 < (J.neg).lo then some ((I.divPositive J.neg h').neg)
  else none

/-- One step of the reciprocal: `G[k] = -(∑_{j=1}^k F[j] G[k-j]) / F[0]`. -/
def invStep (F G : Array RationalInterval) : Option (Array RationalInterval) :=
  (divNonzero (RationalInterval.sum (range G.size) fun j ↦
      (get F (j + 1)).mul (get G (G.size - 1 - j))).neg (get F 0)).map
    fun g ↦ G.push (round g)

/-- `m` steps of the reciprocal. -/
def invLoop (F : Array RationalInterval) :
    ℕ → Array RationalInterval → Option (Array RationalInterval)
  | 0, G => some G
  | m + 1, G => (invStep F G).bind (invLoop F m)

/-- The jet of `1 / f` from the jet `F` of `f`, when `F[0]` does not contain zero. -/
def inv (n : ℕ) (F : Array RationalInterval) : Option (Array RationalInterval) :=
  (divNonzero (RationalInterval.const 1) (get F 0)).bind fun g₀ ↦ invLoop F n #[round g₀]

/-- One step of the exponential: `E[k+1] = (∑_{j=0}^k (j+1) F[j+1] E[k-j]) / (k+1)`. -/
def expStep (F E : Array RationalInterval) : Array RationalInterval :=
  E.push (round ((RationalInterval.const (1 / (E.size : ℚ))).mul
    (RationalInterval.sum (range E.size) fun j ↦
      (RationalInterval.const (j + 1)).mul ((get F (j + 1)).mul (get E (E.size - 1 - j))))))

/-- `m` steps of the exponential. -/
def expLoop (F : Array RationalInterval) : ℕ → Array RationalInterval → Array RationalInterval
  | 0, E => E
  | m + 1, E => expLoop F m (expStep F E)

/-- The jet of `exp ∘ f` from the jet `F` of `f`, with the exponential at Taylor order `order`. -/
def exp (n order : ℕ) (F : Array RationalInterval) : Array RationalInterval :=
  expLoop F n #[round (RationalInterval.expRangeWith (get F 0) order)]

end IntervalJet

/-! ### Soundness -/

namespace IntervalJet

/-- The coefficient `k ≤ n` of the jet `Array.ofFn f` is `f k`. -/
theorem get_ofFn {n : ℕ} (f : Fin (n + 1) → RationalInterval) {k : ℕ} (hk : k ≤ n) :
    get (Array.ofFn f) k = f ⟨k, Nat.lt_succ_of_le hk⟩ := by
  simp [get, Nat.lt_succ_of_le hk]

/-- The coefficient `i` of `G.push v` is that of `G` for `i < G.size` and `v` for `i = G.size`. -/
theorem get_push (G : Array RationalInterval) (v : RationalInterval) {i : ℕ}
    (hi : i < G.size + 1) : get (G.push v) i = if i < G.size then get G i else v := by
  unfold get
  split_ifs with h
  · simp [Array.getElem?_push, Nat.ne_of_lt h, Array.getElem?_eq_getElem h]
  · have : i = G.size := by omega
    subst this
    simp

/-- Outward rounding keeps every member: `round I` contains every member of `I`. -/
theorem round_sound {I : RationalInterval} {x : ℝ} (hx : I.MemReal x) : (round I).MemReal x :=
  RationalInterval.relativeHull_sound roundBits hx

/-- **The Leibniz rule for Taylor coefficients.** -/
theorem iteratedDeriv_mul_div_factorial {f g : ℝ → ℝ} {x : ℝ} {k : ℕ}
    (hf : ContDiffAt ℝ k f x) (hg : ContDiffAt ℝ k g x) :
    iteratedDeriv k (fun y ↦ f y * g y) x / k.factorial =
      ∑ j ∈ range (k + 1), iteratedDeriv j f x / j.factorial *
        (iteratedDeriv (k - j) g x / (k - j).factorial) := by
  rw [iteratedDeriv_fun_mul hf hg, Finset.sum_div]
  refine sum_congr rfl fun j hj ↦ ?_
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hj)
  have h : (k.choose j : ℝ) * j.factorial * (k - j).factorial = k.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hjk
  have h0 : (k.choose j : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hjk).ne'
  have h1 : (j.factorial : ℝ) ≠ 0 := by positivity
  have h2 : ((k - j).factorial : ℝ) ≠ 0 := by positivity
  rw [← h]
  field_simp

end IntervalJet

open IntervalJet

/-- A function with a jet of order `n` on `X` is `C^n` at every point of `X`. -/
theorem JetEncloses.contDiffAt {n : ℕ} {J : Array RationalInterval} {f : ℝ → ℝ}
    {X : RationalInterval} (h : JetEncloses n J f X) {x : ℝ} (hx : X.MemReal x) :
    ContDiffAt ℝ n f x :=
  (h x hx).1

/-- `IntervalJet.const n c` is a jet of the constant `c` on every interval. -/
theorem JetEncloses.const (n : ℕ) (c : ℚ) (X : RationalInterval) :
    JetEncloses n (IntervalJet.const n c) (fun _ ↦ (c : ℝ)) X := by
  intro x _
  refine ⟨contDiffAt_const, fun k hk ↦ ?_⟩
  change (get (IntervalJet.const n c) k).MemReal _
  rw [IntervalJet.const, get_ofFn _ hk, iteratedDeriv_const]
  by_cases h : k = 0
  · subst h; simp
  · simp only [h, ↓reduceIte, zero_div]
    exact_mod_cast RationalInterval.memReal_const 0

/-- `IntervalJet.id n X` is a jet of the identity on `X`. -/
theorem JetEncloses.id (n : ℕ) (X : RationalInterval) :
    JetEncloses n (IntervalJet.id n X) (fun x ↦ x) X := by
  intro x hx
  refine ⟨contDiffAt_id, fun k hk ↦ ?_⟩
  change (get (IntervalJet.id n X) k).MemReal _
  rw [IntervalJet.id, get_ofFn _ hk, iteratedDeriv_fun_id]
  rcases k with _ | _ | k
  · simpa using hx
  · simpa using RationalInterval.memReal_const 1
  · simpa using RationalInterval.memReal_const 0

/-- The coefficientwise sum of jets of `f` and `g` is a jet of `f + g`. -/
theorem JetEncloses.add {n : ℕ} {I J : Array RationalInterval} {f g : ℝ → ℝ}
    {X : RationalInterval} (hI : JetEncloses n I f X) (hJ : JetEncloses n J g X) :
    JetEncloses n (IntervalJet.add n I J) (fun x ↦ f x + g x) X := by
  intro x hx
  obtain ⟨hf, hI'⟩ := hI x hx
  obtain ⟨hg, hJ'⟩ := hJ x hx
  refine ⟨hf.add hg, fun k hk ↦ ?_⟩
  change (get (IntervalJet.add n I J) k).MemReal _
  rw [IntervalJet.add, get_ofFn _ hk, iteratedDeriv_fun_add (hf.of_le (by exact_mod_cast hk))
    (hg.of_le (by exact_mod_cast hk)), add_div]
  exact round_sound (RationalInterval.add_sound (hI' k hk) (hJ' k hk))

/-- The coefficientwise difference of jets of `f` and `g` is a jet of `f - g`. -/
theorem JetEncloses.sub {n : ℕ} {I J : Array RationalInterval} {f g : ℝ → ℝ}
    {X : RationalInterval} (hI : JetEncloses n I f X) (hJ : JetEncloses n J g X) :
    JetEncloses n (IntervalJet.sub n I J) (fun x ↦ f x - g x) X := by
  intro x hx
  obtain ⟨hf, hI'⟩ := hI x hx
  obtain ⟨hg, hJ'⟩ := hJ x hx
  refine ⟨hf.sub hg, fun k hk ↦ ?_⟩
  change (get (IntervalJet.sub n I J) k).MemReal _
  rw [IntervalJet.sub, get_ofFn _ hk, iteratedDeriv_fun_sub (hf.of_le (by exact_mod_cast hk))
    (hg.of_le (by exact_mod_cast hk)), sub_div]
  exact round_sound (RationalInterval.sub_sound (hI' k hk) (hJ' k hk))

/-- `IntervalJet.smul n c I` is a jet of `c f` when `I` is a jet of `f`. -/
theorem JetEncloses.smul {n : ℕ} {I : Array RationalInterval} {f : ℝ → ℝ}
    {X : RationalInterval} (c : ℚ) (hI : JetEncloses n I f X) :
    JetEncloses n (IntervalJet.smul n c I) (fun x ↦ (c : ℝ) * f x) X := by
  intro x hx
  obtain ⟨hf, hI'⟩ := hI x hx
  refine ⟨contDiffAt_const.mul hf, fun k hk ↦ ?_⟩
  change (get (IntervalJet.smul n c I) k).MemReal _
  rw [IntervalJet.smul, get_ofFn _ hk, iteratedDeriv_const_mul _ (hf.of_le (by exact_mod_cast hk)),
    mul_div_assoc]
  exact round_sound (RationalInterval.mul_sound (RationalInterval.memReal_const c) (hI' k hk))

/-- If `I` and `J` enclose `a j` and `b j` for `j ≤ k`, the Cauchy sum `cauchy I J k` encloses
`∑ j ≤ k, a j b (k - j)`. -/
theorem cauchy_sound {I J : Array RationalInterval} {a b : ℕ → ℝ} {k : ℕ}
    (hI : ∀ j ≤ k, (get I j).MemReal (a j)) (hJ : ∀ j ≤ k, (get J j).MemReal (b j)) :
    (cauchy I J k).MemReal (∑ j ∈ range (k + 1), a j * b (k - j)) :=
  RationalInterval.sum_sound fun j hj ↦ RationalInterval.mul_sound
    (hI j (Nat.lt_succ_iff.mp (mem_range.mp hj))) (hJ (k - j) (Nat.sub_le k j))

/-- The Cauchy product of jets of `f` and `g` is a jet of `f g` (the Leibniz rule). -/
theorem JetEncloses.mul {n : ℕ} {I J : Array RationalInterval} {f g : ℝ → ℝ}
    {X : RationalInterval} (hI : JetEncloses n I f X) (hJ : JetEncloses n J g X) :
    JetEncloses n (IntervalJet.mul n I J) (fun x ↦ f x * g x) X := by
  intro x hx
  obtain ⟨hf, hI'⟩ := hI x hx
  obtain ⟨hg, hJ'⟩ := hJ x hx
  refine ⟨hf.mul hg, fun k hk ↦ ?_⟩
  change (get (IntervalJet.mul n I J) k).MemReal _
  rw [IntervalJet.mul, get_ofFn _ hk, iteratedDeriv_mul_div_factorial
    (hf.of_le (by exact_mod_cast hk)) (hg.of_le (by exact_mod_cast hk))]
  exact round_sound (cauchy_sound (fun j hj ↦ hI' j (hj.trans hk))
    (fun j hj ↦ hJ' j (hj.trans hk)))

/-- If `f` is `C^n`, `I` is a jet of `f` on `Y` and `c X ⊆ Y`, then `IntervalJet.scaleArg n c I` is
a jet of `x ↦ f (c x)` on `X`. -/
theorem JetEncloses.scaleArg {n : ℕ} {I : Array RationalInterval} {f : ℝ → ℝ}
    {X Y : RationalInterval} (c : ℚ) (hf : ContDiff ℝ n f) (hI : JetEncloses n I f Y)
    (hXY : ∀ x, X.MemReal x → Y.MemReal ((c : ℝ) * x)) :
    JetEncloses n (IntervalJet.scaleArg n c I) (fun x ↦ f ((c : ℝ) * x)) X := by
  intro x hx
  refine ⟨(hf.comp (contDiff_const.mul contDiff_id)).contDiffAt, fun k hk ↦ ?_⟩
  change (get (IntervalJet.scaleArg n c I) k).MemReal _
  rw [IntervalJet.scaleArg, get_ofFn _ hk,
    iteratedDeriv_comp_const_mul (hf.of_le (by exact_mod_cast hk))]
  have h := RationalInterval.mul_sound (RationalInterval.memReal_const (c ^ k))
    ((hI _ (hXY x hx)).2 k hk)
  push_cast at h
  rw [mul_div_assoc]
  exact round_sound h

/-- A successful `divNonzero I J = some K` certifies `v ≠ 0` and `u / v ∈ K` for `u ∈ I` and
`v ∈ J`. -/
theorem divNonzero_sound {I J K : RationalInterval} (h : divNonzero I J = some K) {u v : ℝ}
    (hu : I.MemReal u) (hv : J.MemReal v) : v ≠ 0 ∧ K.MemReal (u / v) := by
  unfold divNonzero at h
  split_ifs at h with h1 h2 <;> cases h
  · exact ⟨(lt_of_lt_of_le (by exact_mod_cast h1) hv.1).ne',
      RationalInterval.divPositive_sound h1 hu hv⟩
  · have hn := RationalInterval.neg_sound hv
    have := RationalInterval.neg_sound (RationalInterval.divPositive_sound h2 hu hn)
    rw [div_neg, neg_neg] at this
    exact ⟨neg_ne_zero.mp (lt_of_lt_of_le (by exact_mod_cast h2) hn.1).ne', this⟩

/-- The Taylor coefficients of `1 / f` satisfy `(1/f)_k = -(∑_{j < k} f_{j+1} (1/f)_{k-1-j}) / f`
for `k ≥ 1`, from `f (1/f) = 1` near `x`. -/
theorem iteratedDeriv_inv_div_factorial {f : ℝ → ℝ} {x : ℝ} {k : ℕ}
    (hf : ContDiffAt ℝ k f x) (hx : f x ≠ 0) (hk : 0 < k) :
    iteratedDeriv k (fun y ↦ (f y)⁻¹) x / k.factorial =
      -(∑ j ∈ range k, iteratedDeriv (j + 1) f x / (j + 1).factorial *
        (iteratedDeriv (k - 1 - j) (fun y ↦ (f y)⁻¹) x / (k - 1 - j).factorial)) / f x := by
  have hev : (fun y ↦ f y * (f y)⁻¹) =ᶠ[nhds x] fun _ ↦ (1 : ℝ) := by
    filter_upwards [hf.continuousAt.eventually_ne hx] with y hy
    exact mul_inv_cancel₀ hy
  have h := iteratedDeriv_mul_div_factorial (g := fun y ↦ (f y)⁻¹) hf (hf.inv hx)
  rw [hev.iteratedDeriv_eq, iteratedDeriv_const] at h
  simp only [hk.ne', ↓reduceIte, zero_div] at h
  rw [sum_range_succ'] at h
  simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one, Nat.sub_zero] at h
  have e : ∀ j ∈ range k, k - (j + 1) = k - 1 - j := fun j _ ↦ by omega
  rw [sum_congr rfl fun j hj ↦ by rw [e j hj]] at h
  rw [eq_div_iff hx]
  linear_combination -h

/-- If `F` encloses the Taylor coefficients of `f` at `x` with `f x ≠ 0` and `G` encloses the first
coefficients of `1 / f`, a successful `invLoop F m G` adds `m` coefficients and encloses all of
them. -/
theorem invLoop_sound {n : ℕ} {F : Array RationalInterval} {f : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ n f x) (hx : f x ≠ 0)
    (hF : ∀ k ≤ n, (get F k).MemReal (iteratedDeriv k f x / k.factorial)) :
    ∀ (m : ℕ) (G G' : Array RationalInterval), 0 < G.size → G.size + m ≤ n + 1 →
      (∀ i < G.size,
        (get G i).MemReal (iteratedDeriv i (fun y ↦ (f y)⁻¹) x / i.factorial)) →
      invLoop F m G = some G' → G'.size = G.size + m ∧ ∀ i < G'.size,
        (get G' i).MemReal (iteratedDeriv i (fun y ↦ (f y)⁻¹) x / i.factorial)
  | 0, G, G', _, _, hG, h => by
    simp only [invLoop, Option.some.injEq] at h
    subst h
    exact ⟨rfl, hG⟩
  | m + 1, G, G', hpos, hsize, hG, h => by
    simp only [invLoop, Option.bind_eq_some_iff] at h
    obtain ⟨G₁, h1, h2⟩ := h
    simp only [invStep, Option.map_eq_some_iff] at h1
    obtain ⟨g, hg, rfl⟩ := h1
    set k := G.size with hk
    have hkn : k ≤ n := by omega
    have hs : (RationalInterval.sum (range k) fun j ↦
        (get F (j + 1)).mul (get G (k - 1 - j))).MemReal
          (∑ j ∈ range k, iteratedDeriv (j + 1) f x / (j + 1).factorial *
            (iteratedDeriv (k - 1 - j) (fun y ↦ (f y)⁻¹) x / (k - 1 - j).factorial)) :=
      RationalInterval.sum_sound fun j hj ↦ RationalInterval.mul_sound
        (hF (j + 1) (by have := mem_range.mp hj; omega)) (hG _ (by omega))
    have hf0 := hF 0 (Nat.zero_le n)
    simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one] at hf0
    have hgk := (divNonzero_sound hg (RationalInterval.neg_sound hs) hf0).2
    rw [← iteratedDeriv_inv_div_factorial (hf.of_le (by exact_mod_cast hkn)) hx hpos] at hgk
    have ih := invLoop_sound hf hx hF m (G.push (round g)) G' (by simp)
      (by simp only [Array.size_push]; omega) (fun i hi ↦ by
        rw [get_push _ _ (by simpa using hi)]
        split_ifs with h
        · exact hG i h
        · obtain rfl : i = k := by simp only [Array.size_push] at hi; omega
          exact round_sound hgk) h2
    simp only [Array.size_push] at ih
    exact ⟨by omega, ih.2⟩

/-- A successful `IntervalJet.inv n F` is a jet of `1 / f` when `F` is a jet of `f`. -/
theorem JetEncloses.inv {n : ℕ} {F G : Array RationalInterval} {f : ℝ → ℝ}
    {X : RationalInterval} (hF : JetEncloses n F f X) (h : IntervalJet.inv n F = some G) :
    JetEncloses n G (fun x ↦ (f x)⁻¹) X := by
  simp only [IntervalJet.inv, Option.bind_eq_some_iff] at h
  obtain ⟨g₀, hg₀, hloop⟩ := h
  intro x hx
  obtain ⟨hf, hF'⟩ := hF x hx
  have hf0 := hF' 0 (Nat.zero_le n)
  simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one] at hf0
  obtain ⟨hne, hg⟩ := divNonzero_sound hg₀ (RationalInterval.memReal_const 1) hf0
  refine ⟨hf.inv hne, fun k hk ↦ ?_⟩
  have h := invLoop_sound hf hne hF' n #[round g₀] G (by simp) (by simp; omega) (fun i hi ↦ by
    obtain rfl : i = 0 := by simpa using hi
    simpa [IntervalJet.get, one_div] using round_sound hg) hloop
  exact h.2 k (by simp at h; omega)

/-- The Taylor coefficients of `exp ∘ f` satisfy
`(e^f)_{k+1} = (∑_{j ≤ k} (j+1) f_{j+1} (e^f)_{k-j}) / (k+1)`, from `(e^f)' = f' e^f`. -/
theorem iteratedDeriv_exp_div_factorial {f : ℝ → ℝ} {x : ℝ} {k : ℕ}
    (hf : ContDiffAt ℝ (k + 1) f x) :
    iteratedDeriv (k + 1) (fun y ↦ Real.exp (f y)) x / (k + 1).factorial =
      1 / (k + 1 : ℝ) * ∑ j ∈ range (k + 1), (j + 1 : ℝ) *
        (iteratedDeriv (j + 1) f x / (j + 1).factorial *
          (iteratedDeriv (k - j) (fun y ↦ Real.exp (f y)) x / (k - j).factorial)) := by
  have hev : deriv (fun y ↦ Real.exp (f y)) =ᶠ[nhds x]
      fun y ↦ deriv f y * Real.exp (f y) := by
    filter_upwards [hf.eventually (by simp)] with y hy
    rw [_root_.deriv_exp (hy.differentiableAt (by simp)), mul_comm]
  rw [iteratedDeriv_succ', hev.iteratedDeriv_eq]
  have hd : ContDiffAt ℝ k (deriv f) x := hf.derivWithin (by simp)
  have he : ContDiffAt ℝ k (fun y ↦ Real.exp (f y)) x :=
    Real.contDiff_exp.contDiffAt.comp x (hf.of_le (by simp))
  rw [Nat.factorial_succ, Nat.cast_mul, div_mul_eq_div_div_swap,
    iteratedDeriv_mul_div_factorial hd he, one_div_mul_eq_div, Nat.cast_succ]
  congr 1
  refine sum_congr rfl fun j _ ↦ ?_
  rw [← iteratedDeriv_succ', Nat.factorial_succ]
  push_cast
  field_simp

/-- If `F` encloses the Taylor coefficients of `f` at `x` and `E` encloses the first coefficients of
`exp ∘ f`, then `expLoop F m E` adds `m` coefficients and encloses all of them. -/
theorem expLoop_sound {n : ℕ} {F : Array RationalInterval} {f : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ n f x)
    (hF : ∀ k ≤ n, (get F k).MemReal (iteratedDeriv k f x / k.factorial)) :
    ∀ (m : ℕ) (E : Array RationalInterval), 0 < E.size → E.size + m ≤ n + 1 →
      (∀ i < E.size,
        (get E i).MemReal (iteratedDeriv i (fun y ↦ Real.exp (f y)) x / i.factorial)) →
      (expLoop F m E).size = E.size + m ∧ ∀ i < (expLoop F m E).size,
        (get (expLoop F m E) i).MemReal
          (iteratedDeriv i (fun y ↦ Real.exp (f y)) x / i.factorial)
  | 0, E, _, _, hE => ⟨rfl, hE⟩
  | m + 1, E, hpos, hsize, hE => by
    have hpush : ∀ i < (expStep F E).size, (get (expStep F E) i).MemReal
        (iteratedDeriv i (fun y ↦ Real.exp (f y)) x / i.factorial) := by
      intro i hi
      simp only [expStep, Array.size_push] at hi
      simp only [expStep]
      rw [get_push _ _ hi]
      split_ifs with h
      · exact hE i h
      · have hi' : i = E.size := by omega
        obtain ⟨k, hk⟩ : ∃ k, E.size = k + 1 := ⟨E.size - 1, by omega⟩
        rw [hi', hk]
        have hkn : k + 1 ≤ n := by omega
        rw [iteratedDeriv_exp_div_factorial (hf.of_le (by exact_mod_cast hkn))]
        refine round_sound (RationalInterval.mul_sound ?_ (RationalInterval.sum_sound
          fun j hj ↦ RationalInterval.mul_sound ?_ (RationalInterval.mul_sound
            (hF (j + 1) (by have := mem_range.mp hj; omega)) ?_)))
        · simpa using RationalInterval.memReal_const (1 / ((k + 1 : ℕ) : ℚ))
        · simpa using RationalInterval.memReal_const ((j : ℚ) + 1)
        · simpa using hE (k - j) (by have := mem_range.mp hj; omega)
    have hs : (expStep F E).size = E.size + 1 := by simp [expStep]
    have ih := expLoop_sound hf hF m (expStep F E) (by omega) (by omega) hpush
    exact ⟨by rw [expLoop, ih.1, hs]; omega, ih.2⟩

/-- `IntervalJet.exp n order F` is a jet of `exp ∘ f` when `F` is a jet of `f`. -/
theorem JetEncloses.exp {n : ℕ} {F : Array RationalInterval} {f : ℝ → ℝ}
    {X : RationalInterval} (order : ℕ) (hF : JetEncloses n F f X) :
    JetEncloses n (IntervalJet.exp n order F) (fun x ↦ Real.exp (f x)) X := by
  intro x hx
  obtain ⟨hf, hF'⟩ := hF x hx
  refine ⟨Real.contDiff_exp.contDiffAt.comp x hf, fun k hk ↦ ?_⟩
  have hf0 := hF' 0 (Nat.zero_le n)
  simp only [iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one] at hf0
  have h := expLoop_sound hf hF' n
    #[round (RationalInterval.expRangeWith (get F 0) order)] (by simp) (by simp; omega)
    (fun i hi ↦ by
      obtain rfl : i = 0 := by simpa using hi
      simpa [IntervalJet.get] using round_sound (RationalInterval.expRangeWith_sound _ order hf0))
  exact h.2 k (by simp at h; omega)

end CAS.Numerics
