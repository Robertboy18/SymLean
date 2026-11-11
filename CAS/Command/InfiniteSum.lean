/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.Algebra.Basic
public import CAS.Command.Sum
public import Mathlib.Analysis.SpecificLimits.Normed
public meta import Mathlib.Combinatorics.Enumerative.Stirling

/-!
# Infinite sums: `#cas [sum k a ∞]`

`#cas [sum k a ∞] f` sums `f k` for `k = a, a + 1, …`, as Mathematica's
`Sum[f, {k, a, Infinity}]` does, for summands that are sums of terms `c kʲ rᵏ` with rational
`c`, `r` and `|r| < 1` (geometric series, and their products with polynomials). It proves

`HasSum (fun k : ℕ ↦ f (k + a)) S`

with the exact rational `S`: the series converges, unconditionally, and its sum is `S`. The
summand is rewritten, by `ring`, as `∑ cⱼ kᵉʲ rⱼᵏ` after the shift by `a`; Mathlib's
`hasSum_pow_mul_geometric_of_norm_lt_one` gives each term's sum as a finite sum of Stirling
numbers, which `norm_num` evaluates. A term with `|r| ≥ 1` makes the series diverge, and the
command refuses it before any proof. A summand `c / k ^ (2m)` is summed by the zeta values of
`CAS.Command.Zeta`, whose handler of this command leaves every other
summand to the one here.
-/

public meta section

namespace CAS.Command.InfiniteSum

open Lean Elab Command Meta Term
open CAS.Command.InfoView
open CAS.Command.SpecialFunctions

/-- `∑' n, n ^ d * r ^ n` for `|r| < 1`, by Mathlib's formula
`∑ j ≤ d, S(d, j) j! rʲ / (1 - r) ^ (j + 1)`. -/
def powerGeometricSum (degree : Nat) (r : ℚ) : ℚ :=
  (List.range (degree + 1)).foldl (fun total j ↦
    total + (Nat.stirlingSecond degree j * j.factorial : ℚ) * r ^ j / (1 - r) ^ (j + 1)) 0

/-- `P (k + a)` for the coefficient array `P`, lowest degree first. -/
def shiftPoly (P : Array ℚ) (a : ℚ) : Array ℚ := Id.run do
  let mut out : Array ℚ := Array.replicate P.size 0
  for j in [0:P.size] do
    -- `(k + a) ^ j = ∑ i ≤ j, C(j, i) a ^ (j - i) k ^ i`.
    for i in [0:j + 1] do
      out := out.set! i (out.getD i 0 + P.getD j 0 * (Nat.choose j i : ℚ) * a ^ (j - i))
  return out

/-- `a / b ^ k` as `a * (1 / b) ^ k`, so that `k / 2 ^ k` is a polynomial-times-geometric term. -/
def reciprocalPowers : Verified.Expr (Fin 1) → Verified.Expr (Fin 1)
  | .div a (.rpow b (.var i)) => .mul (reciprocalPowers a) (.rpow (.div (.nat 1) b) (.var i))
  | .add a b => .add (reciprocalPowers a) (reciprocalPowers b)
  | .sub a b => .sub (reciprocalPowers a) (reciprocalPowers b)
  | .mul a b => .mul (reciprocalPowers a) (reciprocalPowers b)
  | .neg a => .neg (reciprocalPowers a)
  | other => other

/-- Unfold `Verified.Expr.eval` and turn real powers with natural-number casts as exponents into
natural powers, before any cast is pushed inside: `r ^ ((n + 2 : ℕ) : ℝ)` becomes `r ^ (n + 2)`.
`Digits.cleanProof` then finishes the restatement. -/
def naturalPowers (proof : Lean.Expr) : MetaM Lean.Expr := do
  let mut theorems : SimpTheorems := {}
  theorems ← theorems.addDeclToUnfold ``Verified.Expr.eval
  for name in [``Matrix.cons_val_zero, ``Matrix.cons_val_fin_one, ``Real.rpow_natCast] do
    theorems ← theorems.addConst name
  let context ← Simp.mkContext {} (simpTheorems := #[theorems])
    (congrTheorems := ← getSimpCongrTheorems)
  let (result, _) ← simp (← inferType proof) context
  match result.proof? with
  | none => mkExpectedTypeHint proof result.expr
  | some equality => mkEqMP equality proof

/-- Run `#cas [sum k a ∞] f`. -/
def logInfiniteSum (ref : Syntax) (k : TSyntax `ident) (aStx : Syntax) (input : Syntax) :
    CommandElabM Unit := do
  let a ← parseRational "sum" aStx
  unless a.den = 1 && 0 ≤ a do throwErrorAt aStx "sum: the lower bound must be a natural number"
  let aNat := a.num.toNat
  let reified ← Sum.parseSummand input k.getId
  let f : Verified.Expr (Fin 1) ← match reified with
    | ⟨[_], expression, _⟩ => pure expression
    | _ => throwErrorAt input "sum: the summand must be an expression in {k.getId}"
  let some geo := Sum.toGeoPoly (reciprocalPowers f)
    | throwErrorAt input "sum: infinite sums are computed for sums of terms c k ^ j r ^ k with \
        rational c and r"
  -- The terms `c kᵉ rᵏ` of `f (k + a) = ∑ rᵃ P (k + a) rᵏ`.
  let mut terms : Array (ℚ × Nat × ℚ) := #[]
  for (r, P) in geo do
    let shifted := shiftPoly P a
    for e in [0:shifted.size] do
      let c := shifted.getD e 0 * r ^ aNat
      if c == 0 then continue
      unless |r| < 1 do
        throwErrorAt input "sum: the term with ratio {r} has |{r}| ≥ 1, so the series diverges \
          (Mathlib's tsum of a non-summable series is 0)"
      terms := terms.push (c, e, r)
  let value : ℚ := terms.foldl (fun total (c, e, r) ↦ total + c * powerGeometricSum e r) 0
  let lemmas := Series.seriesCleanLemmas ++ [``Real.rpow_natCast, ``Nat.cast_ofNat,
    ``Matrix.cons_val_zero, ``Int.cast_ofNat, ``Int.cast_neg, ``Nat.cast_id]
  let proof ← liftTermElabM do
    let fT ← exprToSyntax (← quoteVerifiedExpr f)
    let aLit : TSyntax `term := ⟨Syntax.mkNumLit (toString aNat)⟩
    -- The summation variable keeps the user's name.
    let n := mkIdent k.getId
    let real (q : ℚ) : TermElabM (TSyntax `term) := do `(($(← ratSyntax q) : ℝ))
    -- `∑ cⱼ (nᵉʲ rⱼⁿ)` and its `HasSum` from Mathlib's formula.
    let mut sum? : Option (TSyntax `term) := none
    let mut hasSum? : Option (TSyntax `term) := none
    for (c, e, r) in terms do
      let eLit : TSyntax `term := ⟨Syntax.mkNumLit (toString e)⟩
      let term ← `($(← real c) * (($n : ℝ) ^ ($eLit : ℕ) * $(← real r) ^ $n))
      let single ← `((hasSum_pow_mul_geometric_of_norm_lt_one (𝕜 := ℝ) $eLit
        (r := $(← real r)) (by norm_num)).mul_left $(← real c))
      sum? := some (← match sum? with
        | none => pure term
        | some s => `($s + $term))
      hasSum? := some (← match hasSum? with
        | none => pure single
        | some h => `(HasSum.add $h $single))
    -- The Stirling numbers of Mathlib's formula, as facts checked by `decide`.
    let mut facts : Array (TSyntax `tactic) := #[]
    let mut factLemmas : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) := #[]
    let mut seen : Array (Nat × Nat) := #[]
    for (_, e, _) in terms do
      for j in [0:e + 1] do
        if seen.contains (e, j) then continue
        seen := seen.push (e, j)
        let name := mkIdent (Name.mkSimple s!"stirling_{e}_{j}")
        let eLit : TSyntax `term := ⟨Syntax.mkNumLit (toString e)⟩
        let jLit : TSyntax `term := ⟨Syntax.mkNumLit (toString j)⟩
        let vLit : TSyntax `term := ⟨Syntax.mkNumLit (toString (Nat.stirlingSecond e j))⟩
        facts := facts.push (← `(tactic|
          have $name : Nat.stirlingSecond $eLit $jLit = $vLit := by decide))
        factLemmas := factLemmas.push (← `(Lean.Parser.Tactic.simpLemma| $name:ident))
    let point ← if aNat = 0 then `(($n : ℝ)) else `((($n + $aLit : ℕ) : ℝ))
    let factsTac ← if facts.isEmpty then `(tactic| skip) else `(tactic| ($facts;*))
    let summand ← `(Verified.Expr.eval ![$point] $fT)
    let statement ← `(HasSum (fun $n:ident : ℕ ↦ $summand) $(← real value))
    let script ← match sum?, hasSum? with
      | some s, some h => `(tactic| (
          have key : ∀ $n:ident : ℕ, $summand = $s := by
            intro $n:ident
            simp only [Verified.Expr.eval, Matrix.cons_val_zero, Matrix.cons_val_fin_one,
              Real.rpow_natCast, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.cast_ofNat,
              Int.cast_neg, Int.cast_one, Int.cast_zero]
            try push_cast
            try simp only [one_div, inv_pow]
            first | done | ring
          simp only [key]
          $factsTac:tactic
          exact ($h).summable.hasSum_iff.mpr ((HasSum.tsum_eq $h).trans
            (by norm_num [Finset.sum_range_succ, Nat.factorial, $factLemmas,*]))))
      | _, _ => `(tactic| (
          have key : ∀ $n:ident : ℕ, $summand = 0 := by
            intro $n:ident
            simp only [Verified.Expr.eval, Matrix.cons_val_zero, Matrix.cons_val_fin_one,
              Real.rpow_natCast, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, Int.cast_ofNat,
              Int.cast_neg, Int.cast_one, Int.cast_zero]
            try push_cast
            first | done | ring
          simp only [key]
          exact hasSum_zero))
    let proof ← elabCheckedProof "sum" statement (← `(by $script:tactic))
    let cleaned ← Digits.cleanProof (← naturalPowers proof) lemmas
      [``Verified.Expr.univariateEval] (simprocs := true)
    let named := Digits.restoreNames (← inferType proof) (← inferType cleaned)
    let cleaned ← mkExpectedTypeHint cleaned named
    CAS.Tactic.Explanation.kernelCheckedProof "sum" named cleaned
  let report ← liftTermElabM do
    evidenceReportMessage
      #[← CAS.Tactic.Explanation.UncheckedExplanationStep.ofProof "Sum of the series" proof]
  logReport ref {
    domain := s!"{k.getId} ∈ ℕ, {k.getId} ≥ {aNat}"
    input := reified.render
    inputType := "summand"
    output := toString value
    outputType := "sum of the series"
  } #[report]

end CAS.Command.InfiniteSum

namespace CAS.Command

open Lean Elab Command

/-- `#cas [sum k a ∞] e` sums the series of `e` from the natural number `a`, for sums of terms
`c * k ^ j * r ^ k` with rational `c`, `r` and `|r| < 1`, and for `c / k ^ (2 * m)` by the
values of `zeta`; see `#cas [sum k a b]`. It proves `HasSum (fun k : ℕ ↦ e (k + a)) S` with the
exact `S`, which states convergence as well as the value, and refuses a term with `|r| ≥ 1`,
whose series diverges. The tactic `cas` does not prove these statements.
-/
syntax (name := casInfiniteSumCommand) "#cas" "[" &"sum" ident term:max "∞" "]" term : command

elab_rules : command
  | `(#cas [sum $k:ident $a:term ∞] $f:term) => InfiniteSum.logInfiniteSum f k a f

end CAS.Command
