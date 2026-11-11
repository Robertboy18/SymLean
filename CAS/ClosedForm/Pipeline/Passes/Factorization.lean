/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.ClosedForm.Pipeline.Passes.NumericLiteral
public import CAS.Expr.Decomposition

/-!
# Product and additive factorization

The search for a factor shared by all summands of a sum, the extraction it certifies, and the
one-factor removal used by the denominator and square-root passes. The central rewrite is
`a*r₁ + a*r₂ + ... + a*rₖ = a * (r₁ + ... + rₖ)` over the summands of `additiveTerms` and the
factors of `productFactors`. Every step of the extraction rearranges a product or splits off a
nonzero numeric literal, checked when the pass runs, so its theorems are unconditional
equalities in `ℝ`.

## Main definitions

* `extractOneFactor?`, `removeOneFactor?`: given `factor` and `expr`, return `rest` with
  `expr = factor * rest` when `factor` occurs in the product tree of `expr` (or is `expr`
  itself); `extractNumericFactor?` handles an exact rational coefficient by multiplying with
  its reciprocal.
* `findCommonFactor?`, `factorCommonAddTop`, `factorCommonAddDeep`: additive common-factor
  extraction at the top level and recursively; `eval_factorCommonAddDeep` is its soundness.
* `cancelOneFactor?`: remove one occurrence of a factor from a product tree, leaving `1` when
  the factor is the whole expression and reducing an exponent or dividing a natural literal
  where applicable. Unlike `removeOneFactor?` it has no reciprocal fallback and does not look
  under a negation. Denominator cancellation and square-root pairing
  (`deepFactorCancelSidePass`, `sqrtProductCollectSidePass`) are built on it; its soundness
  theorem `eval_cancelOneFactor?` is stated as a quotient and needs `factor ≠ 0`.

## Implementation notes

We read the candidates for `a` off the first summand (`commonFactorCandidates`), check each
against every summand with `removeOneFactor?`, and extract the first one that passes. Only
nontrivial factors are tried (`nontrivialFactor` rejects `0`, `±1`), symbolic candidates come
before numeric ones, and a natural coefficient exposes its divisors, largest first, so that
`2*x + 4*y = 2*(x + 2*y)` is found by the same search. A symbolic candidate has to occur in every
summand, as the summand itself or inside its products, powers and negations. A numeric
candidate `q` also passes a variable, or a numeric literal that it does not divide, which is
read as `q * ((1/q) * t)` (`extractNumericFactor?`). The search is syntactic and computes no
gcd: `factorCommonAddTop` turns `4*x + 6*y` into `4 * (x + 3/2 * y)`. Cancelling the polynomial
gcd of a numerator and a denominator is the job of `Alg.canonical`.
-/

@[expose] public section

namespace CAS.Verified.Expr

/-- Positive natural divisors of a natural literal, largest first, ignoring `1`.

These are only search candidates. The removal check `removeOneFactor?` confirms that
the chosen candidate divides every summand from which it is removed. -/
def natDivisorFactorCandidates {ι : Type*} (n : Nat) : List (Verified.Expr ι) :=
  ((List.range (n + 1)).reverse.filter fun d ↦ decide (d ≠ 0) && decide (d ≠ 1) &&
    decide (n % d = 0)).map fun d ↦ (.nat d : Verified.Expr ι)

/-- Candidate atoms exposed by one multiplicative factor.

If the first additive term contains `x^2`, trying only the whole `x^2` misses sums such as
`x^2 + x*y + x`.  Exposing the base as an earlier candidate lets the common-factor pass extract
`x` directly, while still keeping the original power as a fallback candidate.  Positive natural
coefficients expose their nontrivial divisors so the same pass can find numeric gcd-like common
factors such as `2` in `2*x + 4*y`.
-/
def factorCandidates {ι : Type*} : Verified.Expr ι → List (Verified.Expr ι)
  | .pow base (k + 1) => base :: [(.pow base (k + 1) : Verified.Expr ι)]
  | .nat n => natDivisorFactorCandidates n
  | expr => [expr]

/-- Candidate factors for additive common-factor extraction.

For a negated first term such as `-(x*z) + x*y`, use the factors of the
positive payload. Symbolic factors are tried before numeric coefficient
content: extracting `sqrt c` from every term is structurally more useful than
first extracting a shared integer coefficient. Numeric candidates remain as a
fallback. The extraction routine verifies every candidate with `removeOneFactor?`.
-/
def commonFactorCandidates {ι : Type*} (expr : Verified.Expr ι) :
    List (Verified.Expr ι) :=
  let payload :=
    match expr with
    | .neg a => a
    | expr => expr
  let candidates := (productFactors payload).flatMap factorCandidates
  candidates.filter (fun candidate ↦ (NumericLiteral.parse? candidate).isNone) ++
    candidates.filter (fun candidate ↦ (NumericLiteral.parse? candidate).isSome)

/-- Nontrivial factors are worth extracting from an additive sum.

The common-factor pass is allowed to extract exact numeric factors such as `2` from
`2*x + 2*y`; it ignores `0`, `1`, and `-1`, which either do not help or mostly
shuffle signs.  Positive natural coefficients expose their divisors as candidates, so some
gcd-like cases are handled by the same checked extractor.  Full rational-coefficient content
extraction is not attempted. -/
def nontrivialFactor {ι : Type*} : Verified.Expr ι → Bool
  | .nat n => decide (n ≠ 0) && decide (n ≠ 1)
  | .int z => decide (z ≠ 0) && decide (z ≠ 1) && decide (z ≠ -1)
  | .rat num den =>
      decide (num ≠ 0) && decide (num ≠ (den : Int)) && decide (num ≠ -((den : Int)))
  | _ => true

/-- Remove a known nonzero numeric factor from an arbitrary term by multiplying the term by the
numeric reciprocal.

This is the coefficient-content fallback used for implicit coefficients: if the common candidate is
`1/2`, then a bare term `y` can be read as `(1/2) * (2*y)`.  The result is still checked;
no user side condition is emitted because the candidate has to be an executable nonzero numeric
literal. -/
def extractNumericFactor? {ι : Type*} (factor expr : Verified.Expr ι) :
    Option (Verified.Expr ι) :=
  match NumericLiteral.parse? factor with
  | some qfactor =>
      if qfactor = 0 then
        none
      else
        some (mkMul (mkRatConst (1 / qfactor)) expr)
  | none => none

/-- If `factor` parses as a nonzero rational `q` then `expr = factor * ((1/q) * expr)` in `ℝ`;
this is the equation certifying the numeric-coefficient fallback. -/
theorem eval_extractNumericFactor? {ι : Type*} (ρ : ι → ℝ)
    (factor expr rest : Verified.Expr ι)
    (hextract : extractNumericFactor? factor expr = some rest) :
    expr.eval ρ = factor.eval ρ * rest.eval ρ := by
  unfold extractNumericFactor? at hextract
  cases hf : NumericLiteral.parse? factor with
  | none => simp [hf] at hextract
  | some qfactor =>
      simp only [hf] at hextract
      split_ifs at hextract with hzero
      cases hextract
      rw [NumericLiteral.eval_parse?_eq_some ρ factor qfactor hf, eval_mkMul, eval_mkRatConst]
      norm_num [Rat.cast_div, hzero]

/-- Remove one matching factor from a term, returning the remaining product.

Unlike quotient cancellation, this is a pure equality-preserving extractor and therefore needs no
nonzero side condition.  It also treats atomic terms equal to the factor as `factor * 1`, which is
what makes additive common-factor extraction work for sums such as `x*y + x*z + x`; and it can
extract through a leading negation, so alternating residuals such as `x*y - x*z + x` are handled
by the same pass.
-/
def extractOneFactor? {ι : Type*} [DecidableEq ι] (factor : Verified.Expr ι) :
    Verified.Expr ι → Option (Verified.Expr ι)
  | .mul a b =>
      if a = factor then
        some b
      else if b = factor then
        some a
      else
        match extractOneFactor? factor a with
        | some a' => some (mkMul a' b)
        | none =>
            match extractOneFactor? factor b with
            | some b' => some (mkMul a b')
            | none => none
  | .pow base (k + 1) =>
      if base = factor then
        some (mkPow base k)
      else
        none
  | .neg a =>
      match extractOneFactor? factor a with
      | some rest => some (mkNeg rest)
      | none => none
  | .nat n =>
      if (.nat n : Verified.Expr ι) = factor then
        some 1
      else
        match factor with
        | .nat d =>
            if d = 0 then
              none
            else if n % d = 0 then
              some (.nat (n / d))
            else
              extractNumericFactor? factor (.nat n)
        | _ => extractNumericFactor? factor (.nat n)
  | .int z => if (.int z : Verified.Expr ι) = factor then some 1 else none
  | .rat num den =>
      if (.rat num den : Verified.Expr ι) = factor then
        some 1
      else
        match NumericLiteral.parse? (.rat num den : Verified.Expr ι),
            NumericLiteral.parse? factor with
        | some q, some qfactor =>
            if qfactor = 0 then
              none
            else
              some (mkRatConst (q / qfactor))
        | _, _ => extractNumericFactor? factor (.rat num den)
  | .pi => if (.pi : Verified.Expr ι) = factor then some 1 else none
  | .e => if (.e : Verified.Expr ι) = factor then some 1 else none
  | .var name =>
      if (.var name : Verified.Expr ι) = factor then
        some 1
      else
        extractNumericFactor? factor (.var name)
  | _ => none

/-- Soundness of equality-preserving factor extraction. -/
theorem eval_extractOneFactor? {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (factor expr rest : Verified.Expr ι)
    (hextract : extractOneFactor? factor expr = some rest) :
    expr.eval ρ = factor.eval ρ * rest.eval ρ := by
  induction expr generalizing rest with
  | mul a b ha hb =>
      simp only [extractOneFactor?] at hextract
      split_ifs at hextract with haf hbf
      · cases hextract
        simp [haf]
      · cases hextract
        simp [hbf, mul_comm]
      · split at hextract
        · rename_i a' ha'
          cases hextract
          simp [ha a' ha', mul_assoc]
        · split at hextract
          · rename_i b' hb'
            cases hextract
            simp [hb b' hb', mul_left_comm]
          · cases hextract
  | pow base k =>
      cases k with
      | zero => simp [extractOneFactor?] at hextract
      | succ k =>
          simp only [extractOneFactor?] at hextract
          split_ifs at hextract with hbase
          cases hextract
          simp [hbase, pow_succ']
  | nat n =>
      simp only [extractOneFactor?] at hextract
      split_ifs at hextract with h
      · cases hextract
        simp [← h]
      · cases factor with
        | nat d =>
            simp only at hextract
            split_ifs at hextract with hd hmod
            · cases hextract
              simp only [Verified.Expr.eval]
              exact_mod_cast (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hmod)).symm
            · exact eval_extractNumericFactor? ρ _ _ rest hextract
        | _ => exact eval_extractNumericFactor? ρ _ _ rest hextract
  | int _ | pi | e =>
      simp only [extractOneFactor?] at hextract
      split_ifs at hextract with h
      cases hextract
      simp [← h]
  | rat num den =>
      simp only [extractOneFactor?] at hextract
      split_ifs at hextract with h
      · cases hextract
        simp [← h]
      · split at hextract
        · rename_i q qfactor hq hf
          split_ifs at hextract with hzero
          cases hextract
          rw [NumericLiteral.eval_parse?_eq_some ρ _ q hq,
            NumericLiteral.eval_parse?_eq_some ρ factor qfactor hf, eval_mkRatConst, Rat.cast_div,
            mul_div_cancel₀ _ (Rat.cast_ne_zero.mpr hzero)]
        · exact eval_extractNumericFactor? ρ factor _ rest hextract
  | var name =>
      simp only [extractOneFactor?] at hextract
      split_ifs at hextract with h
      · cases hextract
        simp [← h]
      · exact eval_extractNumericFactor? ρ factor _ rest hextract
  | neg a ha =>
      simp only [extractOneFactor?] at hextract
      split at hextract
      · rename_i r hr
        cases hextract
        simp [ha r hr]
      · cases hextract
  | _ => simp [extractOneFactor?] at hextract

/--
Remove one exact factor, checking whole-expression equality before recursive
product and power extraction.

The whole-expression check is needed for non-polynomial atoms such as
`sqrt a`, `exp a`, and `sin a`, and for a complete power used as a common
factor. The lower-level extractor handles factors nested inside products,
powers, and negations.
-/
def removeOneFactor? {ι : Type*} [DecidableEq ι]
    (factor expr : Verified.Expr ι) : Option (Verified.Expr ι) :=
  if expr = factor then
    some 1
  else
    extractOneFactor? factor expr

/-- Soundness of exact or recursively nested one-factor removal. -/
theorem eval_removeOneFactor? {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (factor expr rest : Verified.Expr ι)
    (hextract : removeOneFactor? factor expr = some rest) :
    expr.eval ρ = factor.eval ρ * rest.eval ρ := by
  unfold removeOneFactor? at hextract
  split_ifs at hextract with heq
  · cases hextract
    simp [heq]
  · exact eval_extractOneFactor? ρ factor expr rest hextract

/-- Extract a chosen common factor from every term in an additive list. -/
def extractCommonRests? {ι : Type*} [DecidableEq ι] (factor : Verified.Expr ι) :
    List (Verified.Expr ι) → Option (List (Verified.Expr ι))
  | [] => some []
  | term :: terms =>
      match removeOneFactor? factor term, extractCommonRests? factor terms with
      | some rest, some rests => some (rest :: rests)
      | _, _ => none

/-- Soundness of extracting a common factor from an additive list. -/
theorem eval_extractCommonRests? {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (factor : Verified.Expr ι) :
    ∀ (terms rests : List (Verified.Expr ι)),
      extractCommonRests? factor terms = some rests →
        (mkAddList terms).eval ρ = factor.eval ρ * (mkAddList rests).eval ρ
  | [], _, h => by
      obtain rfl := Option.some.inj h
      simp [mkAddList]
  | term :: terms, rests, h => by
      simp only [extractCommonRests?] at h
      split at h
      · rename_i rest restTail hterm htail
        cases h
        simp [mkAddList, eval_removeOneFactor? ρ factor term rest hterm,
          eval_extractCommonRests? ρ factor terms restTail htail]
        ring_nf
      · cases h

/-- Search a candidate list for a factor shared by every additive term. -/
def findCommonFactor? {ι : Type*} [DecidableEq ι]
    (terms candidates : List (Verified.Expr ι)) :
    Option (Verified.Expr ι × List (Verified.Expr ι)) :=
  match candidates with
  | [] => none
  | factor :: rest =>
      if nontrivialFactor factor then
        match extractCommonRests? factor terms with
        | some rests => some (factor, rests)
        | none => findCommonFactor? terms rest
      else
        findCommonFactor? terms rest

/-- Soundness of a successful common-factor search. -/
theorem eval_findCommonFactor? {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (terms candidates : List (Verified.Expr ι)) (factor : Verified.Expr ι)
    (rests : List (Verified.Expr ι))
    (hfind : findCommonFactor? terms candidates = some (factor, rests)) :
    (mkAddList terms).eval ρ = factor.eval ρ * (mkAddList rests).eval ρ := by
  induction candidates with
  | nil => simp [findCommonFactor?] at hfind
  | cons candidate candidates ih =>
      simp only [findCommonFactor?] at hfind
      split_ifs at hfind
      · split at hfind
        · cases hfind
          exact eval_extractCommonRests? ρ _ terms _ ‹_›
        · exact ih hfind
      · exact ih hfind

/-- Factor one symbolic term shared by every summand of an additive expression. -/
def factorCommonAddTop {ι : Type*} [DecidableEq ι] (expr : Verified.Expr ι) :
    Verified.Expr ι :=
  match additiveTerms expr with
  | [] => expr
  | [_] => expr
  | first :: restTerms =>
      match findCommonFactor? (first :: restTerms) (commonFactorCandidates first) with
      | some (factor, rests) => mkMul factor (mkAddList rests)
      | none => expr

/-- Soundness of additive common-factor reconstruction. -/
@[simp] theorem eval_factorCommonAddTop {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (expr : Verified.Expr ι) :
    (factorCommonAddTop expr).eval ρ = expr.eval ρ := by
  unfold factorCommonAddTop
  rcases hterms : additiveTerms expr with _ | ⟨first, _ | ⟨second, more⟩⟩
  · simp
  · simp
  · rcases hfind : findCommonFactor? (first :: second :: more) (commonFactorCandidates first) with
      _ | ⟨factor, rests⟩
    · simp [hfind]
    · simp only [hfind, eval_mkMul]
      rw [← eval_findCommonFactor? ρ _ _ factor rests hfind, ← hterms, eval_mkAddList_additiveTerms]

/-- Recursively rebuild an expression and factor common additive terms where possible. -/
def factorCommonAddDeep {ι : Type*} [DecidableEq ι] : Verified.Expr ι → Verified.Expr ι
  | .add a b => factorCommonAddTop (mkAdd (factorCommonAddDeep a) (factorCommonAddDeep b))
  | .mul a b => mkMul (factorCommonAddDeep a) (factorCommonAddDeep b)
  | .sub a b => mkSub (factorCommonAddDeep a) (factorCommonAddDeep b)
  | .div a b => mkDiv (factorCommonAddDeep a) (factorCommonAddDeep b)
  | .neg a => mkNeg (factorCommonAddDeep a)
  | .pow a k => mkPow (factorCommonAddDeep a) k
  | .sin a => mkSin (factorCommonAddDeep a)
  | .cos a => mkCos (factorCommonAddDeep a)
  | .atan a => .atan (factorCommonAddDeep a)
  | .asin a => .asin (factorCommonAddDeep a)
  | .acos a => .acos (factorCommonAddDeep a)
  | .exp a => mkExp (factorCommonAddDeep a)
  | .log a => mkLog (factorCommonAddDeep a)
  | .sqrt a => mkSqrt (factorCommonAddDeep a)
  | .rpow a b => mkRpow (factorCommonAddDeep a) (factorCommonAddDeep b)
  | expr => expr

/-- Recursive common-factor reconstruction preserves real evaluation at every valuation. -/
@[simp] theorem eval_factorCommonAddDeep {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (expr : Verified.Expr ι) :
    (factorCommonAddDeep expr).eval ρ = expr.eval ρ := by
  induction expr <;> simp [factorCommonAddDeep, *]

/-- Remove one matching factor from a product tree: the whole expression when it is the factor,
otherwise a factor anywhere inside a product, one power of a matching base, or a divisor of a
natural literal. -/
def cancelOneFactor? {ι : Type*} [DecidableEq ι] (factor expr : Verified.Expr ι) :
    Option (Verified.Expr ι) :=
  if expr = factor then
    some 1
  else
    match expr with
    | .mul a b =>
        if a = factor then
          some b
        else if b = factor then
          some a
        else
          match cancelOneFactor? factor a with
          | some a' => some (mkMul a' b)
          | none =>
              match cancelOneFactor? factor b with
              | some b' => some (mkMul a b')
              | none => none
    | .pow base (k + 1) =>
        if base = factor then
          some (mkPow base k)
        else
          none
    | .nat n =>
        match factor with
        | .nat d =>
            if d = 0 then
              none
            else if n % d = 0 then
              some (.nat (n / d))
            else
              none
        | _ => none
    | _ =>
        none

/-- Removing a nonzero factor computes the quotient of the original expression. -/
theorem eval_cancelOneFactor? {ι : Type*} [DecidableEq ι] (ρ : ι → ℝ)
    (factor expr rest : Verified.Expr ι)
    (hcancel : cancelOneFactor? factor expr = some rest)
    (hfactor : factor.eval ρ ≠ 0) :
    rest.eval ρ = expr.eval ρ / factor.eval ρ := by
  have hwhole : ∀ whole : Verified.Expr ι, whole = factor → (1 : Verified.Expr ι).eval ρ =
      whole.eval ρ / factor.eval ρ := by
    rintro whole rfl
    simp [hfactor]
  induction expr generalizing rest with
  | mul a b ha hb =>
      rw [cancelOneFactor?.eq_def] at hcancel
      split_ifs at hcancel with hsame
      · cases hcancel
        exact hwhole _ hsame
      simp only at hcancel
      split_ifs at hcancel with haf hbf
      · cases hcancel
        simp [haf, hfactor]
      · cases hcancel
        simp [hbf, hfactor]
      · split at hcancel
        · rename_i a' ha'
          cases hcancel
          simp [ha a' ha', div_mul_eq_mul_div]
        · split at hcancel
          · rename_i b' hb'
            cases hcancel
            simp [hb b' hb', mul_div_assoc']
          · cases hcancel
  | nat n =>
      rw [cancelOneFactor?.eq_def] at hcancel
      split_ifs at hcancel with hsame
      · cases hcancel
        exact hwhole _ hsame
      cases factor with
      | nat d =>
          simp only at hcancel
          split_ifs at hcancel with hd hmod
          cases hcancel
          simp only [Verified.Expr.eval] at hfactor ⊢
          exact Nat.cast_div (Nat.dvd_of_mod_eq_zero hmod) hfactor
      | _ => simp at hcancel
  | pow a k =>
      rw [cancelOneFactor?.eq_def] at hcancel
      split_ifs at hcancel with hsame
      · cases hcancel
        exact hwhole _ hsame
      cases k with
      | zero => simp at hcancel
      | succ k =>
          simp only at hcancel
          split_ifs at hcancel with haf
          cases hcancel
          simp [haf, pow_succ, hfactor]
  | _ =>
      rw [cancelOneFactor?.eq_def] at hcancel
      split_ifs at hcancel with hsame
      cases hcancel
      exact hwhole _ hsame

end CAS.Verified.Expr
