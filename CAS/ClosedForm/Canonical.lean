/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.ClosedForm.Pipeline.Passes.Factorization
public import CAS.ClosedForm.Pipeline.SideClaim
public import CAS.Polynomial.Sparse
public import CAS.Polynomial.Sparse.MultivariateGcd

/-!
# Canonical form of multivariate rational expressions

`Alg.canonicalForm` normalizes the rational fragment of the expression language over opaque
atoms: every subterm that is not built from the field operations, natural powers and numeric
literals (a variable, `π`, `e`, `sin a`, `exp a`, `sqrt a`, a real power, ...) is an atom. The
rational skeleton becomes one numerator over one denominator, polynomials with rational
coefficients in a sorted table of atoms, a common factor is cancelled, and the denominator is
made monic. The arguments of the atoms are canonicalized first, bottom-up, so that reducing
`(x^4 - y^4) / (x^2 - y^2)` inside `sqrt` can make the atom match `sqrt (x^2 + y^2)`.
`eval_canonicalForm` proves that the output has the value of the input wherever the recorded
nonzero conditions hold, and `Alg.canonical` is the same result as a `SideClaimRoute`.

## Main definitions

* `Canonical.compareExpr`, `Canonical.atoms`: the structural order on expressions and the sorted
  atom table of an expression.
* `Canonical.compile`, `Canonical.render`: the two directions between the rational skeleton of an
  expression and the ordered sparse representation over its atoms.
* `Canonical.propose`, `Canonical.Reduction.valid`: the cancellation candidate and its checked
  acceptance test.
* `Canonical.reduceFraction`: one level of rational canonicalization.
* `canonicalForm`, `canonical`: the bottom-up normalizer, and the same result as a
  `SideClaimRoute`.

## Main results

* `Canonical.eval_compile`, `Canonical.eval_render`: under its recorded conditions the compiled
  fraction has the value of the expression, and rendering keeps the value of a sparse
  polynomial at the point of atom values.
* `Canonical.eval_reduceFraction`, `eval_canonicalForm`: one level of reduction, and the whole
  normalizer, preserve evaluation wherever their recorded conditions hold.
* `eval_eq_of_canonicalForm_sub_eq_zero`, `eval_eq_of_canonicalForm_sub_eq`: a canonical form
  `0` of `lhs - rhs` proves `lhs = rhs` under the recorded conditions. The first is the last
  resort of `symbolic_eq`; the second certifies a run read back from the kernel in the identity
  route of `cas` (`DerivativeBridge.certifyCanonicalZeroDifference`).

## Implementation notes

The search proposes and a check decides, as in `RationalCanonical.route` for one variable.
`Canonical.propose` takes a common factor `g` from `Polynomial.Sparse.Multivariate.gcd`, the
recursive gcd by primitive remainder sequences, and the exact quotients `num' = num / g` and
`den' = den / g` from `Polynomial.Sparse.Multivariate.exactQuotient?`, then moves the leading
coefficient of the reduced denominator in graded lexicographic order into `g`, which makes that
denominator monic. The candidate is used only when the sparse normalizations of
`num - g * num'` and `den - g * den'` are empty (`Reduction.valid`, turned into the two
factorization identities by `Reduction.identities`); otherwise the compiled fraction is rendered
unreduced. The rest is proved once: `eval_compile` by induction on the expression, `eval_render`
for the rendering, `eval_rebuild` for the bottom-up pass. When a tactic certifies a run with
`decide +kernel` the kernel runs the gcd search too, but no theorem about it is used, so a wrong
or fuel-exhausted candidate costs a cancellation and never soundness.

We check the candidate instead of proving the gcd algorithm correct, since soundness needs only
that `g` divides, not that it is greatest. The price is that there is no uniqueness theorem for
the output syntax and no completeness theorem for equality testing. With a true gcd the result
is the classical canonical form of a rational function, with coprime numerator and denominator
and a monic denominator, in which the atoms are read as indeterminates; sorting the atoms by
`Canonical.compareExpr` makes it independent of the order in which they occur, so `x + y` and
`y + x` get the same form. Totalized division needs extra bookkeeping: the recorded side
conditions are the numerators of the divisors that a cross-multiplication inside the
expression relies on (adding `1/x` to anything records `x ≠ 0`, while the lone quotient
`sin x / x` records nothing) and, when a nonconstant factor `g` is cancelled, `g ≠ 0` split into
its symbolic factors (`nonvanishingObligations`). The latter is exactly the hypothesis of the
cancellation `(g * num') / (g * den') = num' / den'`; it is implied by the nonvanishing of the
denominator, and it is the denominator itself whenever the fraction reduces to a polynomial, as in
`(x^4 - y^4) / (x^2 - y^2) = x^2 + y^2` under `x^2 - y^2 ≠ 0`. Cancelling a nonzero constant and
rewriting a polynomial into its ordered form are unconditional, so they record nothing.
-/

@[expose] public section

namespace CAS.Verified.Expr.Alg

namespace Canonical

/-! ### A structural order on expressions

Sorting the atoms by a total order makes the normal form independent of the order in which the
atoms are encountered, so that `x + y` and `y + x` receive the same form. The order compares
constructor tags first and then the fields from left to right; variables are compared through
`Ord ι`. -/

/-- Constructor tag of an expression, the primary key of the structural order. -/
def tag {ι : Type*} : Verified.Expr ι → Nat
  | .nat _ => 0
  | .int _ => 1
  | .rat _ _ => 2
  | .pi => 3
  | .e => 4
  | .var _ => 5
  | .add _ _ => 6
  | .mul _ _ => 7
  | .sub _ _ => 8
  | .div _ _ => 9
  | .neg _ => 10
  | .pow _ _ => 11
  | .sin _ => 12
  | .cos _ => 13
  | .atan _ => 14
  | .asin _ => 15
  | .acos _ => 16
  | .exp _ => 17
  | .log _ => 18
  | .sqrt _ => 19
  | .rpow _ _ => 20

/-- Lexicographic combination of two comparison results: the second decides only a tie. -/
def lexOrdering : Ordering → Ordering → Ordering
  | .eq, second => second
  | first, _ => first

/-- Structural total order on expressions over an ordered variable type. -/
def compareExpr {ι : Type*} [Ord ι] : Verified.Expr ι → Verified.Expr ι → Ordering
  | .nat a, .nat b => compare a b
  | .int a, .int b => compare a b
  | .rat num₁ den₁, .rat num₂ den₂ => lexOrdering (compare num₁ num₂) (compare den₁ den₂)
  | .var i, .var j => compare i j
  | .add a₁ b₁, .add a₂ b₂ => lexOrdering (compareExpr a₁ a₂) (compareExpr b₁ b₂)
  | .mul a₁ b₁, .mul a₂ b₂ => lexOrdering (compareExpr a₁ a₂) (compareExpr b₁ b₂)
  | .sub a₁ b₁, .sub a₂ b₂ => lexOrdering (compareExpr a₁ a₂) (compareExpr b₁ b₂)
  | .div a₁ b₁, .div a₂ b₂ => lexOrdering (compareExpr a₁ a₂) (compareExpr b₁ b₂)
  | .neg a, .neg b => compareExpr a b
  | .pow a k, .pow b l => lexOrdering (compareExpr a b) (compare k l)
  | .sin a, .sin b => compareExpr a b
  | .cos a, .cos b => compareExpr a b
  | .atan a, .atan b => compareExpr a b
  | .asin a, .asin b => compareExpr a b
  | .acos a, .acos b => compareExpr a b
  | .exp a, .exp b => compareExpr a b
  | .log a, .log b => compareExpr a b
  | .sqrt a, .sqrt b => compareExpr a b
  | .rpow a₁ b₁, .rpow a₂ b₂ => lexOrdering (compareExpr a₁ a₂) (compareExpr b₁ b₂)
  | a, b => compare (tag a) (tag b)

/-- Insert an expression into a list sorted by `compareExpr`, after every smaller entry. The sort
is written out here because the kernel evaluates it inside module files, which do not see the
bodies of the library sorting functions. -/
def insertSorted {ι : Type*} [Ord ι] (a : Verified.Expr ι) :
    List (Verified.Expr ι) → List (Verified.Expr ι)
  | [] => [a]
  | b :: rest => if compareExpr a b = .gt then b :: insertSorted a rest else a :: b :: rest

/-- Insertion sort by `compareExpr`. -/
def sortExprs {ι : Type*} [Ord ι] : List (Verified.Expr ι) → List (Verified.Expr ι)
  | [] => []
  | a :: rest => insertSorted a (sortExprs rest)

/-- Inserting an expression permutes it to the front. -/
theorem perm_insertSorted {ι : Type*} [Ord ι] (a : Verified.Expr ι) :
    ∀ l : List (Verified.Expr ι), (insertSorted a l).Perm (a :: l)
  | [] => List.Perm.refl _
  | b :: rest => by
      unfold insertSorted
      split
      · exact ((perm_insertSorted a rest).cons b).trans (List.Perm.swap a b rest)
      · exact List.Perm.refl _

/-- Sorting permutes a list. -/
theorem perm_sortExprs {ι : Type*} [Ord ι] :
    ∀ l : List (Verified.Expr ι), (sortExprs l).Perm l
  | [] => List.Perm.refl _
  | a :: rest => (perm_insertSorted a (sortExprs rest)).trans ((perm_sortExprs rest).cons a)

/-- The atoms of the rational skeleton of an expression, with repetitions: every maximal subterm
that is not a field operation, a natural power, or a numeral. -/
def skeletonAtoms {ι : Type*} : Verified.Expr ι → List (Verified.Expr ι)
  | .nat _ => []
  | .int _ => []
  | .rat _ _ => []
  | .add a b => skeletonAtoms a ++ skeletonAtoms b
  | .sub a b => skeletonAtoms a ++ skeletonAtoms b
  | .mul a b => skeletonAtoms a ++ skeletonAtoms b
  | .div a b => skeletonAtoms a ++ skeletonAtoms b
  | .neg a => skeletonAtoms a
  | .pow a _ => skeletonAtoms a
  | atom => [atom]

/-- The atom table of an expression: its distinct atoms in the structural order. -/
def atoms {ι : Type*} [DecidableEq ι] [Ord ι] (expr : Verified.Expr ι) : List (Verified.Expr ι) :=
  sortExprs (skeletonAtoms expr).dedup

/-- Every atom of the skeleton is in the atom table. -/
theorem mem_atoms {ι : Type*} [DecidableEq ι] [Ord ι] {expr atom : Verified.Expr ι}
    (h : atom ∈ skeletonAtoms expr) : atom ∈ atoms expr := by
  unfold atoms
  rw [(perm_sortExprs _).mem_iff, List.mem_dedup]
  exact h

/-- The atom table has no repeated entries. -/
theorem nodup_atoms {ι : Type*} [DecidableEq ι] [Ord ι] (expr : Verified.Expr ι) :
    (atoms expr).Nodup :=
  (perm_sortExprs _).nodup_iff.mpr (List.nodup_dedup _)

/-! ### The sparse representation over the atom table -/

/-- The exponent vector of one atom: `1` at its position in the table, `0` elsewhere. -/
def indicator {ι : Type*} [DecidableEq ι] (table : List (Verified.Expr ι))
    (atom : Verified.Expr ι) : MvMonomial table.length :=
  fun i ↦ if table.get i = atom then 1 else 0

/-- The values of the atoms at an assignment, as the Euclidean point at which sparse polynomials
over the atom table are evaluated. -/
noncomputable def atomPoint {ι : Type*} (table : List (Verified.Expr ι)) (ρ : ι → ℝ) :
    ℝ^(table.length) :=
  WithLp.toLp 2 fun i ↦ (table.get i).eval ρ

/-- The indicator monomial of an entry of the (repetition-free) atom table evaluates to the value
of that atom. -/
theorem mvMonomialVal_indicator {ι : Type*} [DecidableEq ι] (table : List (Verified.Expr ι))
    (ρ : ι → ℝ) (hnodup : table.Nodup) {atom : Verified.Expr ι} (hmem : atom ∈ table) :
    mvMonomialVal (atomPoint table ρ) (indicator table atom) = atom.eval ρ := by
  obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hmem
  unfold mvMonomialVal
  rw [← Fin.prod_univ_def, Finset.prod_eq_single j]
  · simp [indicator, atomPoint]
  · intro i _ hij
    simp only [indicator, ite_eq_right (mt hnodup.get_inj_iff.mp hij), pow_zero]
  · simp

/-! ### Rendering the sparse representation

Terms are written in the descending graded lexicographic order of `mvNormalize`, each as a rational
coefficient times the product of the atoms with positive exponent, negative coefficients as
subtractions. Products use the raw multiplication constructor so that no smart constructor merges
two atoms into a new one (`mkMul` combines `exp a * exp b`); the acceptance test compares atoms
syntactically and must see the same atoms as the input. -/

/-- The product of the atoms with positive exponent, each raised to its exponent. -/
def renderMonomial {ι : Type*} (table : List (Verified.Expr ι)) (mono : MvMonomial table.length) :
    Verified.Expr ι :=
  mulList <| (List.finRange table.length).filterMap fun i ↦
    if mono i = 0 then none else some (mkPow (table.get i) (mono i))

/-- Rendering a monomial preserves its value at the atom point. -/
theorem eval_renderMonomial {ι : Type*} (table : List (Verified.Expr ι)) (ρ : ι → ℝ)
    (mono : MvMonomial table.length) :
    (renderMonomial table mono).eval ρ = mvMonomialVal (atomPoint table ρ) mono := by
  unfold renderMonomial mvMonomialVal
  rw [eval_mulList]
  have hpoint : ∀ i, (atomPoint table ρ).ofLp i = (table.get i).eval ρ := fun _ ↦ rfl
  simp only [hpoint]
  generalize List.finRange table.length = indices
  induction indices with
  | nil => simp
  | cons i rest ih =>
      by_cases h : mono i = 0
      · simp only [List.filterMap_cons, h, ↓reduceIte, ih, List.map_cons, List.prod_cons,
          pow_zero, one_mul]
      · simp only [List.filterMap_cons, h, ↓reduceIte, List.map_cons, List.prod_cons, ih,
          eval_mkPow]

/-- A coefficient times a rendered monomial. -/
def renderTerm {ι : Type*} (table : List (Verified.Expr ι)) (coeff : Rat)
    (mono : MvMonomial table.length) : Verified.Expr ι :=
  mkMul (mkRatConst coeff) (renderMonomial table mono)

/-- Rendering a term preserves its value at the atom point. -/
theorem eval_renderTerm {ι : Type*} (table : List (Verified.Expr ι)) (ρ : ι → ℝ) (coeff : Rat)
    (mono : MvMonomial table.length) :
    (renderTerm table coeff mono).eval ρ =
      (coeff : ℝ) * mvMonomialVal (atomPoint table ρ) mono := by
  simp [renderTerm, eval_renderMonomial]

/-- Append rendered terms to an accumulated sum, subtracting terms with negative coefficient. -/
def renderSum {ι : Type*} [DecidableEq ι] (table : List (Verified.Expr ι)) :
    Verified.Expr ι → List (Rat × MvMonomial table.length) → Verified.Expr ι
  | acc, [] => acc
  | acc, term :: rest =>
      renderSum table
        (if term.1 < 0 then mkSub acc (renderTerm table (-term.1) term.2)
          else mkAdd acc (renderTerm table term.1 term.2)) rest

/-- The rendered sum evaluates to the accumulator plus the value of the appended terms. -/
theorem eval_renderSum {ι : Type*} [DecidableEq ι] (table : List (Verified.Expr ι)) (ρ : ι → ℝ) :
    ∀ (terms : List (Rat × MvMonomial table.length)) (acc : Verified.Expr ι),
      (renderSum table acc terms).eval ρ = acc.eval ρ + mvPolyVal (atomPoint table ρ) terms := by
  intro terms
  induction terms with
  | nil => simp [renderSum, mvPolyVal]
  | cons term rest ih =>
      intro acc
      rw [renderSum, ih]
      split <;> simp [mvPolyVal, mvTermVal, eval_renderTerm] <;> ring

/-- Render a sparse polynomial over the atom table in canonical order. -/
def render {ι : Type*} [DecidableEq ι] (table : List (Verified.Expr ι))
    (poly : MvPoly table.length) : Verified.Expr ι :=
  match mvNormalize poly with
  | [] => .nat 0
  | term :: rest => renderSum table (renderTerm table term.1 term.2) rest

/-- Rendering preserves the value of a sparse polynomial at the atom point. -/
theorem eval_render {ι : Type*} [DecidableEq ι] (table : List (Verified.Expr ι)) (ρ : ι → ℝ)
    (poly : MvPoly table.length) :
    (render table poly).eval ρ = mvPolyVal (atomPoint table ρ) poly := by
  unfold render
  rw [← mvPolyVal_normalize]
  split <;> simp [*, mvPolyVal, mvTermVal, eval_renderSum, eval_renderTerm]

/-- Write a numerator over a denominator, omitting a denominator `1`; a quotient with numerator
`0` or denominator `0` is `0` under total division. -/
def renderFraction {ι : Type*} [DecidableEq ι] (num den : Verified.Expr ι) : Verified.Expr ι :=
  if den = .nat 1 then num
  else if num = .nat 0 ∨ den = .nat 0 then .nat 0
  else .div num den

/-- The rendered fraction evaluates to the quotient of its parts under total division. -/
theorem eval_renderFraction {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ) (num den : Verified.Expr ι) :
    (renderFraction num den).eval ρ = num.eval ρ / den.eval ρ := by
  unfold renderFraction
  split_ifs with hden hzero
  · simp [hden]
  · rcases hzero with rfl | rfl <;> simp
  · rfl

/-! ### The untrusted cancellation candidate and its checked acceptance -/

/-- A proposed cancellation in the sparse representation over the atom table: `num` and `den`
should equal `factor * numerator` and `factor * denominator`. -/
structure Reduction (k : Nat) where
  /-- The common factor to cancel. -/
  factor : MvPoly k
  /-- The reduced numerator. -/
  numerator : MvPoly k
  /-- The reduced denominator, scaled to leading coefficient `1`. -/
  denominator : MvPoly k

/-- Propose the cancellation of the gcd candidate of `num` and `den`, scaled so that the reduced
denominator is monic. A zero numerator is proposed as `0 / den` with the factor `1`, since `0 / den`
is `0` unconditionally, and when an exact quotient by the candidate fails only the scaling is
proposed. -/
def propose {k : Nat} (num den : MvPoly k) : Reduction k :=
  if (mvNormalize num).isEmpty then
    { factor := [(1, mvOne k)], numerator := [], denominator := den }
  else
    let common := Polynomial.Sparse.Multivariate.gcd num den
    let (factor, numerator, denominator) :=
      match Polynomial.Sparse.Multivariate.exactQuotient? num common,
          Polynomial.Sparse.Multivariate.exactQuotient? den common with
      | some numerator, some denominator => (common, numerator, denominator)
      | _, _ => ([(1, mvOne k)], num, den)
    let scale : Rat :=
      match mvLeadingTerm? (mvNormalize denominator) with
      | none => 1
      | some lead => lead.1
    { factor := mvScaleMonomial scale (mvOne k) factor
      numerator := mvScaleMonomial (1 / scale) (mvOne k) numerator
      denominator := mvScaleMonomial (1 / scale) (mvOne k) denominator }

/-- The checked acceptance test: the sparse normalizations of `num - factor * numerator` and
`den - factor * denominator` are both zero. -/
def Reduction.valid {k : Nat} (num den : MvPoly k) (reduction : Reduction k) : Bool :=
  Polynomial.Sparse.isZero (mvSub num (mvMulPoly reduction.factor reduction.numerator)) &&
    Polynomial.Sparse.isZero (mvSub den (mvMulPoly reduction.factor reduction.denominator))

/-- A sparse polynomial accepted as zero evaluates to zero at every point. -/
theorem mvPolyVal_eq_zero_of_isZero {k : Nat} (x : ℝ^k) {poly : MvPoly k}
    (h : Polynomial.Sparse.isZero poly = true) : mvPolyVal x poly = 0 := by
  unfold Polynomial.Sparse.isZero at h
  rw [← mvPolyVal_normalize, List.isEmpty_iff.mp h]
  rfl

/-- An accepted reduction satisfies both factorization identities at every point. -/
theorem Reduction.identities {k : Nat} {num den : MvPoly k} {reduction : Reduction k}
    (hvalid : reduction.valid num den = true) (x : ℝ^k) :
    mvPolyVal x num = mvPolyVal x reduction.factor * mvPolyVal x reduction.numerator ∧
      mvPolyVal x den = mvPolyVal x reduction.factor * mvPolyVal x reduction.denominator := by
  simp only [valid, Bool.and_eq_true] at hvalid
  have hnum := mvPolyVal_eq_zero_of_isZero x hvalid.1
  have hden := mvPolyVal_eq_zero_of_isZero x hvalid.2
  rw [mvPolyVal_sub, mvPolyVal_mulPoly, sub_eq_zero] at hnum hden
  exact ⟨hnum, hden⟩

/-- The value of a sparse polynomial that is a nonzero constant. -/
def constantValue? {k : Nat} (poly : MvPoly k) : Option Rat :=
  match mvNormalize poly with
  | [(coeff, mono)] => if mono = mvOne k ∧ coeff ≠ 0 then some coeff else none
  | _ => none

/-- A nonzero constant polynomial does not vanish. -/
theorem mvPolyVal_ne_zero_of_constantValue? {k : Nat} (x : ℝ^k) {poly : MvPoly k} {coeff : Rat}
    (h : constantValue? poly = some coeff) : mvPolyVal x poly ≠ 0 := by
  unfold constantValue? at h
  split at h
  · rename_i coeff' mono hnorm
    split_ifs at h with hcond
    rw [← mvPolyVal_normalize, hnorm, hcond.1]
    simpa [mvPolyVal, mvTermVal, mvMonomialVal, mvOne] using hcond.2
  · cases h

/-! ### Side conditions of a cancellation -/

/-- Whether an expression is a nonzero rational literal, whose nonvanishing needs no
obligation. -/
def nonzeroLiteral {ι : Type*} : Verified.Expr ι → Bool
  | .rat num den => decide (num ≠ 0) && decide (den ≠ 0)
  | _ => false

/-- A nonzero rational literal does not vanish. -/
theorem eval_ne_zero_of_nonzeroLiteral {ι : Type*} (ρ : ι → ℝ) {expr : Verified.Expr ι}
    (h : nonzeroLiteral expr = true) : expr.eval ρ ≠ 0 := by
  cases expr <;> simp_all [nonzeroLiteral]

/-- Factor-level obligations sufficient for the nonvanishing of an expression: the factor common
to all its summands is extracted, products and positive powers are split into their factors, and
nonzero rational literals are dropped. -/
def nonvanishingObligations {ι : Type*} [DecidableEq ι] (expr : Verified.Expr ι) :
    List (Verified.Expr ι) :=
  (sideFactors (factorCommonAddDeep expr)).filter fun factor ↦ !nonzeroLiteral factor

/-- The factor-level obligations imply that the expression is nonzero. -/
theorem eval_ne_zero_of_nonvanishingObligations {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (expr : Verified.Expr ι) (h : SideHolds ρ (nonvanishingObligations expr)) :
    expr.eval ρ ≠ 0 := by
  rw [← eval_factorCommonAddDeep]
  refine eval_ne_zero_of_sideFactors ρ _ fun factor hfactor ↦ ?_
  by_cases hlit : nonzeroLiteral factor = true
  · exact eval_ne_zero_of_nonzeroLiteral ρ hlit
  · exact h factor (List.mem_filter.mpr ⟨hfactor, by simpa using hlit⟩)

/-- The obligations recorded for cancelling `factor`: none for a nonzero constant, and the
factor-level obligations of the rendered factor otherwise. The cancellation
`(g * num') / (g * den') = num' / den'` needs exactly `g ≠ 0`; since `g` divides the denominator,
this is implied by the nonvanishing of the denominator and coincides with it whenever the fraction
reduces to a polynomial. -/
def cancellationObligations {ι : Type*} [DecidableEq ι] (table : List (Verified.Expr ι))
    (factor : MvPoly table.length) : List (Verified.Expr ι) :=
  match constantValue? factor with
  | some _ => []
  | none => nonvanishingObligations (render table factor)

/-- Under the recorded obligations an accepted reduction has a nonvanishing factor, so the
reduced fraction has the value of the original one. -/
theorem eval_renderFraction_of_valid {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (table : List (Verified.Expr ι)) (num den : MvPoly table.length)
    (reduction : Reduction table.length) (hvalid : reduction.valid num den = true)
    (hobligations : SideHolds ρ (cancellationObligations table reduction.factor)) :
    (renderFraction (render table reduction.numerator)
      (render table reduction.denominator)).eval ρ =
        mvPolyVal (atomPoint table ρ) num / mvPolyVal (atomPoint table ρ) den := by
  obtain ⟨hnumId, hdenId⟩ := reduction.identities hvalid (atomPoint table ρ)
  have hfactor : mvPolyVal (atomPoint table ρ) reduction.factor ≠ 0 := by
    unfold cancellationObligations at hobligations
    split at hobligations
    · exact mvPolyVal_ne_zero_of_constantValue? (atomPoint table ρ) ‹_›
    · have hfactorNe := eval_ne_zero_of_nonvanishingObligations ρ _ hobligations
      rwa [eval_render] at hfactorNe
  rw [eval_renderFraction, eval_render, eval_render, hnumId, hdenId,
    mul_div_mul_left _ _ hfactor]

/-! ### Compiling the rational skeleton

The skeleton of an expression (its field operations and natural powers) is compiled to one
numerator over one denominator in the sparse representation over the atom table. Only a sum or
difference of two fractions relies on nonvanishing: `a/b + c/d = (a*d + c*b)/(b*d)` needs `b ≠ 0`
and `d ≠ 0`, while products, quotients, negations, and powers of fractions are identities of
Mathlib's total division. Each compiled fraction therefore carries the obligations `divisors`
sufficient for its denominator to be nonzero (the canonical renderings of the numerators of the
quotients it contains, split into factors), and a sum or difference records the divisors of its
two operands as its conditions `nonzero`. -/

/-- A fraction over the atom table together with its recorded conditions. -/
structure Fraction (k : Nat) (ι : Type*) where
  /-- The numerator. -/
  num : MvPoly k
  /-- The denominator. -/
  den : MvPoly k
  /-- Conditions under which the fraction has the value of the compiled expression. -/
  nonzero : List (Verified.Expr ι)
  /-- Obligations sufficient for the denominator to be nonzero. -/
  divisors : List (Verified.Expr ι)

/-- The constant polynomial `1`. -/
def one (k : Nat) : MvPoly k :=
  [(1, mvOne k)]

/-- Compile the rational skeleton of an expression over the atom table, which must contain its
atoms. -/
def compile {ι : Type*} [DecidableEq ι] (table : List (Verified.Expr ι)) :
    Verified.Expr ι → Fraction table.length ι
  | .nat n => ⟨[((n : Rat), mvOne _)], one _, [], []⟩
  | .int z => ⟨[((z : Rat), mvOne _)], one _, [], []⟩
  | .rat num den => ⟨[(Rat.divInt num den, mvOne _)], one _, [], []⟩
  | .add a b =>
      let fa := compile table a
      let fb := compile table b
      ⟨mvAdd (mvMulPoly fa.num fb.den) (mvMulPoly fb.num fa.den), mvMulPoly fa.den fb.den,
        fa.nonzero ++ fb.nonzero ++ (fa.divisors ++ fb.divisors), fa.divisors ++ fb.divisors⟩
  | .sub a b =>
      let fa := compile table a
      let fb := compile table b
      ⟨mvSub (mvMulPoly fa.num fb.den) (mvMulPoly fb.num fa.den), mvMulPoly fa.den fb.den,
        fa.nonzero ++ fb.nonzero ++ (fa.divisors ++ fb.divisors), fa.divisors ++ fb.divisors⟩
  | .mul a b =>
      let fa := compile table a
      let fb := compile table b
      ⟨mvMulPoly fa.num fb.num, mvMulPoly fa.den fb.den, fa.nonzero ++ fb.nonzero,
        fa.divisors ++ fb.divisors⟩
  | .div a b =>
      let fa := compile table a
      let fb := compile table b
      ⟨mvMulPoly fa.num fb.den, mvMulPoly fa.den fb.num, fa.nonzero ++ fb.nonzero,
        fa.divisors ++ (fb.divisors ++ nonvanishingObligations (render table fb.num))⟩
  | .neg a =>
      let fa := compile table a
      ⟨mvSub [] fa.num, fa.den, fa.nonzero, fa.divisors⟩
  | .pow a k =>
      let fa := compile table a
      ⟨mvPowPoly fa.num k, mvPowPoly fa.den k, fa.nonzero, fa.divisors⟩
  | atom => ⟨[(1, indicator table atom)], one _, [], []⟩

/-- The constant `1` evaluates to `1`. -/
theorem mvPolyVal_one {k : Nat} (x : ℝ^k) : mvPolyVal x (one k) = 1 := by
  simp [one, mvPolyVal, mvTermVal, mvMonomialVal, mvOne]

/-- A compiled atom is that atom over `1`. -/
theorem eval_compile_atom {ι : Type*} [DecidableEq ι] (table : List (Verified.Expr ι))
    (ρ : ι → ℝ) (hnodup : table.Nodup) {atom : Verified.Expr ι} (hmem : atom ∈ table) :
    mvPolyVal (atomPoint table ρ) [(1, indicator table atom)] /
      mvPolyVal (atomPoint table ρ) (one _) = atom.eval ρ := by
  rw [mvPolyVal_one, div_one]
  simp [mvPolyVal, mvTermVal, mvMonomialVal_indicator table ρ hnodup hmem]

/-- Under its divisor obligations, a compiled denominator is nonzero. -/
theorem den_ne_zero_of_compile {ι : Type*} [DecidableEq ι] (table : List (Verified.Expr ι))
    (ρ : ι → ℝ) :
    ∀ expr : Verified.Expr ι, SideHolds ρ (compile table expr).divisors →
      mvPolyVal (atomPoint table ρ) (compile table expr).den ≠ 0 := by
  intro expr
  induction expr with
  | add a b iha ihb | sub a b iha ihb | mul a b iha ihb =>
      intro hside
      dsimp only [compile] at hside ⊢
      rw [mvPolyVal_mulPoly]
      exact mul_ne_zero (iha hside.append_left) (ihb hside.append_right)
  | div a b iha _ =>
      intro hside
      dsimp only [compile] at hside ⊢
      have hnum := eval_ne_zero_of_nonvanishingObligations ρ _ hside.append_right.append_right
      rw [eval_render] at hnum
      rw [mvPolyVal_mulPoly]
      exact mul_ne_zero (iha hside.append_left) hnum
  | neg a ih => exact ih
  | pow a k ih =>
      intro hside
      dsimp only [compile] at hside ⊢
      rw [mvPolyVal_powPoly]
      exact pow_ne_zero k (ih hside)
  | _ => simp [compile, mvPolyVal_one]

/-- Soundness of the compilation: under its recorded conditions, the compiled fraction has the
value of the expression, provided the (repetition-free) table contains the atoms. -/
theorem eval_compile {ι : Type*} [DecidableEq ι] (table : List (Verified.Expr ι)) (ρ : ι → ℝ)
    (hnodup : table.Nodup) :
    ∀ expr : Verified.Expr ι, (∀ atom ∈ skeletonAtoms expr, atom ∈ table) →
      SideHolds ρ (compile table expr).nonzero →
        mvPolyVal (atomPoint table ρ) (compile table expr).num /
          mvPolyVal (atomPoint table ρ) (compile table expr).den = expr.eval ρ := by
  intro expr
  induction expr with
  | nat n | int z => simp [compile, mvPolyVal_one, mvPolyVal, mvTermVal, mvMonomialVal, mvOne]
  | rat num den =>
      simp [compile, mvPolyVal_one, mvPolyVal, mvTermVal, mvMonomialVal, mvOne]
  | add a b iha ihb | sub a b iha ihb =>
      intro hcover hside
      obtain ⟨hcoverA, hcoverB⟩ := List.forall_mem_append.mp hcover
      dsimp only [compile] at hside ⊢
      have hda := den_ne_zero_of_compile table ρ a hside.append_right.append_left
      have hdb := den_ne_zero_of_compile table ρ b hside.append_right.append_right
      simp only [mvPolyVal_add, mvPolyVal_sub, mvPolyVal_mulPoly, eval]
      rw [← iha hcoverA hside.append_left.append_left, ← ihb hcoverB hside.append_left.append_right]
      field_simp
  | mul a b iha ihb | div a b iha ihb =>
      intro hcover hside
      obtain ⟨hcoverA, hcoverB⟩ := List.forall_mem_append.mp hcover
      dsimp only [compile] at hside ⊢
      rw [mvPolyVal_mulPoly, mvPolyVal_mulPoly, eval, ← iha hcoverA hside.append_left,
        ← ihb hcoverB hside.append_right]
      simp only [div_mul_div_comm, div_div_div_eq]
  | neg a ih =>
      intro hcover hside
      dsimp only [compile] at hside ⊢
      rw [mvPolyVal_sub, eval, ← ih hcover hside]
      simp only [mvPolyVal, zero_sub, neg_div]
  | pow a k ih =>
      intro hcover hside
      dsimp only [compile] at hside ⊢
      rw [mvPolyVal_powPoly, mvPolyVal_powPoly, eval, ← ih hcover hside, div_pow]
  | _ =>
      intro hcover _
      exact eval_compile_atom table ρ hnodup (hcover _ (by simp [skeletonAtoms]))

/-! ### One level of canonicalization -/

/-- Canonicalize the rational structure of an expression whose atoms are already in normal form.

The skeleton is compiled over the sorted atom table, the gcd candidate is proposed, and the reduced
fraction is used when `Reduction.valid` accepts it; otherwise the compiled fraction itself is
rendered. In both cases the conditions are those of the compilation, plus the cancelled factor. -/
def reduceFraction {ι : Type*} [DecidableEq ι] [Ord ι] (expr : Verified.Expr ι) : NormResult ι :=
  let table := atoms expr
  let fraction := compile table expr
  let reduction := propose fraction.num fraction.den
  if reduction.valid fraction.num fraction.den then
    { expr :=
        renderFraction (render table reduction.numerator) (render table reduction.denominator)
      nonzero := cleanSide (fraction.nonzero ++ cancellationObligations table reduction.factor) }
  else
    { expr := renderFraction (render table fraction.num) (render table fraction.den)
      nonzero := cleanSide fraction.nonzero }

/-- One level of canonicalization preserves evaluation wherever its recorded conditions hold. -/
theorem eval_reduceFraction {ι : Type*} [DecidableEq ι] [Ord ι] (ρ : ι → ℝ)
    (expr : Verified.Expr ι) (hside : SideHolds ρ (reduceFraction expr).nonzero) :
    (reduceFraction expr).expr.eval ρ = expr.eval ρ := by
  dsimp only [reduceFraction] at hside ⊢
  have hcompile := eval_compile _ ρ (nodup_atoms expr) expr fun _ h ↦ mem_atoms h
  split_ifs at hside ⊢ with hvalid
  · have hboth := sideHolds_of_cleanSide hside
    rw [eval_renderFraction_of_valid ρ _ _ _ _ hvalid hboth.append_right]
    exact hcompile hboth.append_left
  · rw [eval_renderFraction, eval_render, eval_render]
    exact hcompile (sideHolds_of_cleanSide hside)

/-- Canonicalize the rational structure of a rebuilt subexpression and accumulate its
conditions. -/
def reduceResult {ι : Type*} [DecidableEq ι] [Ord ι] (result : NormResult ι) : NormResult ι :=
  let reduced := reduceFraction result.expr
  { expr := reduced.expr, nonzero := cleanSide (result.nonzero ++ reduced.nonzero) }

/-- The reduction of a rebuilt subexpression preserves its evaluation and implies the conditions
inherited from the rebuilding. -/
theorem eval_reduceResult {ι : Type*} [DecidableEq ι] [Ord ι] (ρ : ι → ℝ) (result : NormResult ι)
    (hside : SideHolds ρ (reduceResult result).nonzero) :
    (reduceResult result).expr.eval ρ = result.expr.eval ρ ∧ SideHolds ρ result.nonzero :=
  ⟨eval_reduceFraction ρ result.expr (sideHolds_of_cleanSide hside).append_right,
    (sideHolds_of_cleanSide hside).append_left⟩

/-! ### Bottom-up canonicalization -/

/-- Rebuild an expression with the argument of every atom in canonical form.

The field operations are rebuilt with their raw constructors and left to the reduction of the
enclosing level; the arguments of the elementary functions and of real powers are canonicalized
here, so that atoms whose arguments reduce to the same expression become syntactically equal. -/
def rebuild {ι : Type*} [DecidableEq ι] [Ord ι] : Verified.Expr ι → NormResult ι
  | .add a b =>
      let ra := rebuild a
      let rb := rebuild b
      { expr := .add ra.expr rb.expr, nonzero := ra.nonzero ++ rb.nonzero }
  | .sub a b =>
      let ra := rebuild a
      let rb := rebuild b
      { expr := .sub ra.expr rb.expr, nonzero := ra.nonzero ++ rb.nonzero }
  | .mul a b =>
      let ra := rebuild a
      let rb := rebuild b
      { expr := .mul ra.expr rb.expr, nonzero := ra.nonzero ++ rb.nonzero }
  | .div a b =>
      let ra := rebuild a
      let rb := rebuild b
      { expr := .div ra.expr rb.expr, nonzero := ra.nonzero ++ rb.nonzero }
  | .neg a =>
      let ra := rebuild a
      { expr := .neg ra.expr, nonzero := ra.nonzero }
  | .pow a k =>
      let ra := rebuild a
      { expr := .pow ra.expr k, nonzero := ra.nonzero }
  | .sin a =>
      let ra := reduceResult (rebuild a)
      { expr := .sin ra.expr, nonzero := ra.nonzero }
  | .cos a =>
      let ra := reduceResult (rebuild a)
      { expr := .cos ra.expr, nonzero := ra.nonzero }
  | .atan a =>
      let ra := reduceResult (rebuild a)
      { expr := .atan ra.expr, nonzero := ra.nonzero }
  | .asin a =>
      let ra := reduceResult (rebuild a)
      { expr := .asin ra.expr, nonzero := ra.nonzero }
  | .acos a =>
      let ra := reduceResult (rebuild a)
      { expr := .acos ra.expr, nonzero := ra.nonzero }
  | .exp a =>
      let ra := reduceResult (rebuild a)
      { expr := .exp ra.expr, nonzero := ra.nonzero }
  | .log a =>
      let ra := reduceResult (rebuild a)
      { expr := .log ra.expr, nonzero := ra.nonzero }
  | .sqrt a =>
      let ra := reduceResult (rebuild a)
      { expr := .sqrt ra.expr, nonzero := ra.nonzero }
  | .rpow a b =>
      let ra := reduceResult (rebuild a)
      let rb := reduceResult (rebuild b)
      { expr := .rpow ra.expr rb.expr, nonzero := ra.nonzero ++ rb.nonzero }
  | expr => { expr := expr, nonzero := [] }

/-- Rebuilding preserves evaluation wherever the accumulated conditions hold. -/
theorem eval_rebuild {ι : Type*} [DecidableEq ι] [Ord ι] (ρ : ι → ℝ) :
    ∀ expr : Verified.Expr ι,
      SideHolds ρ (rebuild expr).nonzero → (rebuild expr).expr.eval ρ = expr.eval ρ := by
  intro expr
  induction expr with
  | add a b iha ihb | sub a b iha ihb | mul a b iha ihb | div a b iha ihb =>
      intro hside
      dsimp only [rebuild] at hside ⊢
      simp only [eval, iha hside.append_left, ihb hside.append_right]
  | neg a ih | pow a _ ih =>
      intro hside
      simp only [rebuild, eval, ih hside]
  | sin a ih | cos a ih | atan a ih | asin a ih | acos a ih | exp a ih | log a ih | sqrt a ih =>
      intro hside
      dsimp only [rebuild] at hside ⊢
      obtain ⟨hvalue, hinner⟩ := eval_reduceResult ρ (rebuild a) hside
      simp only [eval, hvalue, ih hinner]
  | rpow a b iha ihb =>
      intro hside
      dsimp only [rebuild] at hside ⊢
      obtain ⟨hvalueA, hinnerA⟩ := eval_reduceResult ρ (rebuild a) hside.append_left
      obtain ⟨hvalueB, hinnerB⟩ := eval_reduceResult ρ (rebuild b) hside.append_right
      simp only [eval, hvalueA, hvalueB, iha hinnerA, ihb hinnerB]
  | _ => exact fun _ ↦ rfl

end Canonical

/-! ### The normalizer and its route -/

/-- The canonical form of a rational expression over its atoms, with the conditions under which it
equals the input: the arguments of all atoms are canonicalized bottom-up, then the rational
structure of the whole expression is reduced. -/
def canonicalForm {ι : Type*} [DecidableEq ι] [Ord ι] (expr : Verified.Expr ι) : NormResult ι :=
  Canonical.reduceResult (Canonical.rebuild expr)

/-- The canonical form has the value of the input wherever its recorded conditions hold. -/
theorem eval_canonicalForm {ι : Type*} [DecidableEq ι] [Ord ι] (ρ : ι → ℝ)
    (expr : Verified.Expr ι) (hside : SideHolds ρ (canonicalForm expr).nonzero) :
    (canonicalForm expr).expr.eval ρ = expr.eval ρ := by
  obtain ⟨hvalue, hinner⟩ := Canonical.eval_reduceResult ρ (Canonical.rebuild expr) hside
  exact hvalue.trans (Canonical.eval_rebuild ρ expr hinner)

/-- The canonical form as a checked claim: the input, its canonical form, the recorded
conditions, and the soundness proof. -/
def canonical {ι : Type*} [DecidableEq ι] [Ord ι] (expr : Verified.Expr ι) :
    SideClaimRoute ι where
  lhs := expr
  rhs := (canonicalForm expr).expr
  nonzero := (canonicalForm expr).nonzero
  steps := [{ name := "rational-canonical", kind := .sideConditioned }]
  sound := fun ρ hside ↦ eval_canonicalForm ρ expr hside

/-- The canonicalization route records the original expression as its source. -/
@[simp] theorem canonical_lhs {ι : Type*} [DecidableEq ι] [Ord ι] (expr : Verified.Expr ι) :
    (canonical expr).lhs = expr :=
  rfl

/-- The route's result is the expression computed by rational canonicalization. -/
@[simp] theorem canonical_rhs {ι : Type*} [DecidableEq ι] [Ord ι] (expr : Verified.Expr ι) :
    (canonical expr).rhs = (canonicalForm expr).expr := by
  dsimp only [canonical]

/-- The route retains every nonzero condition emitted by canonicalization. -/
@[simp] theorem canonical_nonzero {ι : Type*} [DecidableEq ι] [Ord ι] (expr : Verified.Expr ι) :
    (canonical expr).nonzero = (canonicalForm expr).nonzero :=
  rfl

/-- A canonical form that is literally `0` proves that the input vanishes wherever the recorded
conditions hold. -/
theorem eval_eq_zero_of_canonicalForm_eq_zero {ι : Type*} [DecidableEq ι] [Ord ι] (ρ : ι → ℝ)
    (expr : Verified.Expr ι) (hside : SideHolds ρ (canonicalForm expr).nonzero)
    (hzero : (canonicalForm expr).expr = (0 : Verified.Expr ι)) :
    expr.eval ρ = 0 := by
  rw [← eval_canonicalForm ρ expr hside, hzero]
  simp [Verified.Expr.eval]

/-- A canonical form of `lhs - rhs` that is literally `0` proves the equality wherever the recorded
conditions hold. This is the zero test of the exact tactics; it can also identify atoms whose
arguments reduce to the same rational expression. -/
theorem eval_eq_of_canonicalForm_sub_eq_zero {ι : Type*} [DecidableEq ι] [Ord ι] (ρ : ι → ℝ)
    (lhs rhs : Verified.Expr ι)
    (hside : SideHolds ρ (canonicalForm (lhs - rhs)).nonzero)
    (hzero : (canonicalForm (lhs - rhs)).expr = (0 : Verified.Expr ι)) :
    lhs.eval ρ = rhs.eval ρ :=
  sub_eq_zero.mp (eval_eq_zero_of_canonicalForm_eq_zero ρ (lhs - rhs) hside hzero)

/-- The equation form of the zero test, for a run of the canonical form read back from the
kernel: a computed result `⟨0, side⟩` proves the equality wherever `side` holds. -/
theorem eval_eq_of_canonicalForm_sub_eq {ι : Type*} [DecidableEq ι] [Ord ι]
    (lhs rhs : Verified.Expr ι) (ρ : ι → ℝ) (side : List (Verified.Expr ι))
    (hrun : canonicalForm (.sub lhs rhs) = ⟨.nat 0, side⟩) (hside : SideHolds ρ side) :
    lhs.eval ρ = rhs.eval ρ := by
  have hvalue := eval_canonicalForm ρ (.sub lhs rhs) (hrun ▸ hside)
  simp only [hrun, Verified.Expr.eval, Nat.cast_zero] at hvalue
  exact sub_eq_zero.mp hvalue.symm

end CAS.Verified.Expr.Alg
