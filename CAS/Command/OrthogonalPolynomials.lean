/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Analysis.SpecialFunctions.OrthogonalPolynomials
public import CAS.Command.Zeta
public import CAS.Command.SpecialFunctions
public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.RingTheory.Polynomial.Hermite.Basic
public meta import CAS.Analysis.SpecialFunctions.OrthogonalPolynomials

/-!
# Chebyshev, Hermite and Bernoulli polynomials

A call such as `#cas (ChebyshevT 5 x)` prints a classical polynomial in monomials, as
Mathematica's `ChebyshevT[n, x]` does, and proves the expansion for Mathlib's own polynomial. The
variable may have any name; at a rational number in its place the call proves the exact value.

* `ChebyshevT n x`, `ChebyshevU n x`: `∀ (R : Type*) [CommRing R], Polynomial.Chebyshev.T R n = …`
  (and `Polynomial.Chebyshev.U R n = …`) in `R[X]`, for every commutative ring `R : Type`, from
  Mathlib's recurrence `Chebyshev.T_add_two` (`Chebyshev.U_add_two`).
* `HermiteHe n x`: Mathlib's `Polynomial.hermite n`, the probabilists' Hermite polynomial
  `Heₙ` (SymPy's `hermite_prob`), in `ℤ[X]`, by `Polynomial.hermite_succ`.
* `HermiteH n x`: Mathematica's `HermiteH[n, x]`, the physicists' polynomial
  `Hₙ (x) = 2 ^ (n / 2) Heₙ (√2 x)`. Mathlib defines only `Heₙ`, so the theorem is stated through
  it: `∀ x : ℝ, √2 ^ n * Polynomial.aeval (√2 * x) (Polynomial.hermite n) = …` with integer
  coefficients.
* `BernoulliB n x`: Mathematica's `BernoulliB[n, x]`, Mathlib's `Polynomial.bernoulli n`:
  `∀ x : ℝ, Polynomial.aeval x (Polynomial.bernoulli n) = …`, from
  `Polynomial.coeff_bernoulli` and the integer Bernoulli numerators `bernoulliNumerators n`.

`#cas [N d] (ChebyshevT n q)` (also `ChebyshevU`, `HermiteH`, `HermiteHe`, `BernoulliB`) adds to
the exact value `v` at a rational `q` its first `d` significant digits, truncated toward zero,
with `1 ≤ d ≤ 2000` as for `#cas [N d] e`. The theorem states both: the value, and the decimal
bounds of `#cas [N d] e` (`m / 10 ^ k ≤ P(q) < (m + 1) / 10 ^ k` for a positive value). The
output prints `v = digits` when the digits are exact and `v ≈ digits` otherwise.
`CAS.Command.Calls` reads the calls in all three forms.

## Implementation notes

Each proof evaluates the family's coefficient list at degree `n` in the kernel and rewrites
with the theorem of `CAS/Analysis/SpecialFunctions/OrthogonalPolynomials.lean` that identifies
the list with Mathlib's polynomial for every degree (`chebyshevT_eq_intPoly`,
`chebyshevU_eq_intPoly`, `hermite_eq_intPoly`, `sqrt_two_pow_mul_aeval_hermite`,
`bernoulli_eq_intPoly`), then normalizes once with `ring`. The degrees are at
most 80 for `ChebyshevT`, `ChebyshevU` and `HermiteHe`, and at most 60 for `HermiteH` and
`BernoulliB` (`Family.maxDegree`). As calls of `CAS.Command.FunctionTable`, the families take
any variable, any closed integer expression as the degree, and the syntax of the other
functions.
-/

public meta section

namespace CAS.Command.OrthogonalPolynomials

open Lean Elab Command Meta Term
open CAS.Command.InfoView
open CAS.Command.Digits
open CAS.Continuum
open CAS.Analysis.SpecialFunctions (chebyshevCoeffs hermiteCoeffs physHermiteCoeffs
  bernoulliPolyNumerators)

/-- The polynomial family of a command. -/
inductive Family where
  | chebyshevT | chebyshevU | hermiteHe | hermiteH | bernoulli
  deriving BEq, Inhabited

/-- The command name of a family: Mathematica's name, and `HermiteHe` for Mathlib's probabilists'
Hermite polynomials. -/
def Family.name : Family → String
  | .chebyshevT => "ChebyshevT"
  | .chebyshevU => "ChebyshevU"
  | .hermiteHe => "HermiteHe"
  | .hermiteH => "HermiteH"
  | .bernoulli => "BernoulliB"

/-- The integer list that the kernel evaluates for a family at degree `n`: the coefficients,
lowest degree first, from the lists of `CAS.Analysis.SpecialFunctions.OrthogonalPolynomials`, and
for `bernoulli` the coefficients times `(n + 1)!` (`bernoulliPolyNumerators`). -/
def intCoefficients (family : Family) (n : Nat) : List ℤ :=
  match family with
  | .chebyshevT => (chebyshevCoeffs [0, 1] n).1
  | .chebyshevU => (chebyshevCoeffs [0, 2] n).1
  | .hermiteHe => hermiteCoeffs n
  | .hermiteH => physHermiteCoeffs n
  | .bernoulli => bernoulliPolyNumerators n

/-- The coefficients of a family at degree `n`, lowest degree first; for `bernoulli`,
`Bₙ (x) = ∑ C(n, i) B_{n-i} xⁱ`. -/
def coefficients (family : Family) (n : Nat) : Array ℚ :=
  let scale : ℚ := if family == .bernoulli then (n + 1).factorial else 1
  ((intCoefficients family n).map fun c : ℤ ↦ (c : ℚ) / scale).toArray

/-- An integer list as term syntax of type `List ℤ`. -/
def intListSyntax (l : List ℤ) : TermElabM (TSyntax `term) := do
  let entries ← l.toArray.mapM fun c ↦ do
    let magnitude : TSyntax `term := ⟨Syntax.mkNumLit (toString c.natAbs)⟩
    if c < 0 then `(-$magnitude) else pure magnitude
  `(([$entries,*] : List ℤ))

/-- `∑ cⱼ atom ^ j`, highest degree first, with integer coefficients as numerals (`ring`
normalizes them in any commutative ring) and others as rational literals, each through `cast`. -/
def polySyntax (atom : TSyntax `term) (coefficients : Array ℚ)
    (cast : TSyntax `term → TermElabM (TSyntax `term)) : TermElabM (TSyntax `term) := do
  let constant (c : ℚ) : TermElabM (TSyntax `term) := do
    if c.den = 1 then cast ⟨Syntax.mkNumLit (toString c.num.natAbs)⟩
    else cast (← ratSyntax c)
  let monomial (c : ℚ) (j : Nat) : TermElabM (TSyntax `term) := do
    let power ← match j with
      | 1 => pure atom
      | _ => `($atom ^ $(⟨Syntax.mkNumLit (toString j)⟩))
    if j = 0 then constant c
    else if c = 1 then pure power
    else `($(← constant c) * $power)
  let nonzero := ((coefficients.toList.zipIdx.filter (·.1 != 0))).reverse
  match nonzero with
  | [] => cast ⟨Syntax.mkNumLit "0"⟩
  | (c, j) :: rest =>
      let first ← if c < 0 then `(-$(← monomial (-c) j)) else monomial c j
      rest.foldlM (fun total (c, j) ↦ do
        if c < 0 then `($total - $(← monomial (-c) j)) else `($total + $(← monomial c j)))
        first

/-- The monomial text `16*x^5 - 20*x^3 + 5*x`, in the variable `var`. -/
def polyText (coefficients : Array ℚ) (var : String := "x") : String :=
  SpecialFunctions.renderPolynomial coefficients.toList var

/-- The tactic closing `intPoly R [c₀, c₁, …] = …` (or its value at `x`, with `evaluate`) for a
literal list: unfold the list and the integer casts, then one `ring` normalization. -/
def expandTactic (evaluate : Bool) : TermElabM (TSyntax `tactic) :=
  if evaluate then
    `(tactic| ((simp only [CAS.Analysis.SpecialFunctions.intPoly_cons,
        CAS.Analysis.SpecialFunctions.intPoly_nil, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_intCast, Polynomial.eval_zero, Polynomial.eval_ofNat,
        Polynomial.eval_neg, Polynomial.eval_one, Int.cast_ofNat, Int.cast_neg, Int.cast_one,
        Int.cast_zero]) <;> ring))
  else
    `(tactic| ((simp only [CAS.Analysis.SpecialFunctions.intPoly_cons,
        CAS.Analysis.SpecialFunctions.intPoly_nil, Int.cast_ofNat, Int.cast_neg, Int.cast_one,
        Int.cast_zero]) <;> ring))

/-- The statement and proof script of a polynomial family at degree `n`. The kernel evaluates the
family's coefficient list at `n` (`decide +kernel`), the theorem of
`CAS.Analysis.SpecialFunctions.OrthogonalPolynomials` for the family identifies it with Mathlib's
polynomial, and one `ring` normalization gives the monomials. The real families bind the
variable `var`. -/
def familyStatement (family : Family) (n : Nat) (var : Name := `x) :
    TermElabM (TSyntax `term × TSyntax `tactic × Array ℚ) := do
  let nLit : TSyntax `term := ⟨Syntax.mkNumLit (toString n)⟩
  let R := mkIdent `R
  let x := mkIdent var
  let coefficients := coefficients family n
  match family with
  | .chebyshevT | .chebyshevU =>
      let second := family == .chebyshevU
      let X ← `((Polynomial.X : Polynomial $R))
      let rhs ← polySyntax X coefficients fun t ↦ `(($t : Polynomial $R))
      let lhs ← if second then `(Polynomial.Chebyshev.U $R $nLit)
        else `(Polynomial.Chebyshev.T $R $nLit)
      let identity ← if second then `(CAS.Analysis.SpecialFunctions.chebyshevU_eq_intPoly $R $nLit)
        else `(CAS.Analysis.SpecialFunctions.chebyshevT_eq_intPoly $R $nLit)
      let first ← if second then `([0, 2]) else `([0, 1])
      let list ← intListSyntax (intCoefficients family n)
      return (← `(∀ ($R : Type) [CommRing $R], $lhs = $rhs),
        ← `(tactic| (
          intro $R:ident _
          refine ($identity).trans ?_
          rw [show (CAS.Analysis.SpecialFunctions.chebyshevCoeffs $first $nLit).1 = $list by
            decide +kernel]
          $(← expandTactic false):tactic)), coefficients)
  | .hermiteHe =>
      let X ← `((Polynomial.X : Polynomial ℤ))
      let rhs ← polySyntax X coefficients fun t ↦ `(($t : Polynomial ℤ))
      let list ← intListSyntax (intCoefficients family n)
      return (← `(Polynomial.hermite $nLit = $rhs),
        ← `(tactic| (
          rw [CAS.Analysis.SpecialFunctions.hermite_eq_intPoly,
            show CAS.Analysis.SpecialFunctions.hermiteCoeffs $nLit = $list by decide +kernel]
          $(← expandTactic false):tactic)), coefficients)
  | .hermiteH =>
      let rhs ← polySyntax x coefficients fun t ↦ `(($t : ℝ))
      let list ← intListSyntax (intCoefficients family n)
      return (← `(∀ $x:ident : ℝ,
          √(2 : ℝ) ^ $nLit * Polynomial.aeval (√(2 : ℝ) * $x) (Polynomial.hermite $nLit) = $rhs),
        ← `(tactic| (
          intro $x:ident
          rw [CAS.Analysis.SpecialFunctions.sqrt_two_pow_mul_aeval_hermite,
            show CAS.Analysis.SpecialFunctions.physHermiteCoeffs $nLit = $list by decide +kernel]
          $(← expandTactic true):tactic)), coefficients)
  | .bernoulli =>
      let rhs ← polySyntax x coefficients fun t ↦ `(($t : ℝ))
      let scale := (n + 1).factorial
      let list ← intListSyntax (intCoefficients family n)
      let scaleLit : TSyntax `term := ⟨Syntax.mkNumLit (toString scale)⟩
      return (← `(∀ $x:ident : ℝ, Polynomial.aeval $x (Polynomial.bernoulli $nLit) = $rhs),
        ← `(tactic| (
          intro $x:ident
          rw [CAS.Analysis.SpecialFunctions.bernoulli_eq_intPoly,
            show CAS.Analysis.SpecialFunctions.bernoulliPolyNumerators $nLit = $list by
              decide +kernel,
            show Nat.factorial ($nLit + 1) = $scaleLit by decide +kernel]
          simp only [map_mul, Polynomial.aeval_C, eq_ratCast, Rat.cast_inv, Rat.cast_natCast,
            Nat.cast_ofNat, CAS.Analysis.SpecialFunctions.intPoly_cons,
            CAS.Analysis.SpecialFunctions.intPoly_nil, map_add, map_intCast, Polynomial.aeval_X,
            map_zero, map_neg, map_one, map_ofNat, Int.cast_ofNat, Int.cast_neg, Int.cast_one,
            Int.cast_zero]
          ring)), coefficients)

/-- The largest degree accepted for a family. At these degrees a command costs about 14 G
instructions (`ChebyshevT 80`) and 10 G (`BernoulliB 60`) beyond its imports. With the default
options the same proof script succeeded at `ChebyshevT 90`, `ChebyshevU 90`, `HermiteHe 90`,
`HermiteH 70` and `BernoulliB 70`, and failed on `simp`'s maximum recursion depth at degree 100
for the first three and at degree 80 for the other two. -/
def Family.maxDegree : Family → Nat
  | .chebyshevT | .chebyshevU | .hermiteHe => 80
  | .hermiteH | .bernoulli => 60

/-- Run `#cas (ChebyshevT n x)` and the other polynomial calls, in the variable `var`. -/
def logFamily (ref : Syntax) (family : Family) (n : Nat) (var : Name := `x) :
    CommandElabM Unit := do
  if n > family.maxDegree then
    throwErrorAt ref "{family.name} accepts degrees up to {family.maxDegree}"
  let (proposition, proof, coefficients) ← liftTermElabM do
    let (statement, script, coefficients) ← familyStatement family n var
    let (proposition, proof) ← Algebra.proveStatement family.name statement script
    return (proposition, proof, coefficients)
  let objectText := match family with
    | .chebyshevT => s!"Polynomial.Chebyshev.T R {n}, every commutative ring R : Type"
    | .chebyshevU => s!"Polynomial.Chebyshev.U R {n}, every commutative ring R : Type"
    | .hermiteHe => s!"Polynomial.hermite {n} (probabilists'), ℤ[X]"
    | .hermiteH =>
        s!"√2 ^ {n} Polynomial.hermite {n} (√2 {var}) (physicists'), {var} ∈ ℝ"
    | .bernoulli => s!"Polynomial.bernoulli {n}, {var} ∈ ℝ"
  logReport ref {
    domain := objectText
    input := s!"{family.name} {n} {var}"
    inputType := s!"polynomial in {var}"
    output := polyText coefficients (renderName var)
    outputType := if family == .bernoulli then "polynomial with exact rational coefficients"
      else "polynomial with integer coefficients"
  } #[← liftTermElabM <| Algebra.checkedEvidence family.name
    s!"Monomial expansion of {family.name} {n}" proposition proof]

/-- Run `#cas (ChebyshevT n q)` and the other families at a rational `q`: the exact value, and
with `digits = some d` (`#cas [N d] (ChebyshevT n q)`) its first `d` significant digits. The call
`input` is refused when `Arguments.polyEvalBelow?` needs a number with more than
`Arguments.maxResultDigits` digits to evaluate the value. -/
def logFamilyValue (ref : Syntax) (digits : Option Nat) (family : Family) (n : Nat)
    (argument : Syntax) (input : Syntax) : CommandElabM Unit := do
  if let some d := digits then checkDigitCount ref "N" d
  if n > family.maxDegree then
    throwErrorAt input "{family.name} accepts degrees up to {family.maxDegree}"
  let q ← SpecialFunctions.parseRational (if digits.isSome then "N" else family.name) argument
  let some value := Arguments.polyEvalBelow? (coefficients family n).toList q
    | Arguments.refuseEvaluationSize family.name input
  let outcome? := SpecialFunctions.valueOutcome? digits value
  let nLit : TSyntax `term := ⟨Syntax.mkNumLit (toString n)⟩
  let (proposition, proof) ← liftTermElabM do
    let qT ← `(($(← ratSyntax q) : ℝ))
    let vT ← `(($(← ratSyntax value) : ℝ))
    let (identity, script, _) ← familyStatement family n
    let lhs ← match family with
      | .chebyshevT => `((Polynomial.Chebyshev.T ℝ $nLit).eval $qT)
      | .chebyshevU => `((Polynomial.Chebyshev.U ℝ $nLit).eval $qT)
      | .hermiteHe => `(Polynomial.aeval $qT (Polynomial.hermite $nLit))
      | .hermiteH =>
          `(√(2 : ℝ) ^ $nLit * Polynomial.aeval (√(2 : ℝ) * $qT) (Polynomial.hermite $nLit))
      | .bernoulli => `(Polynomial.aeval $qT (Polynomial.bernoulli $nLit))
    -- `simp` may already close the goal (a value `0`), hence `<;>`.
    let use ← match family with
      | .chebyshevT | .chebyshevU => `(tactic| (rw [hP ℝ]; simp <;> norm_num))
      | .hermiteHe => `(tactic| (
          rw [hP]
          simp only [map_sub, map_add, map_mul, map_neg, map_pow, Polynomial.aeval_X, map_ofNat,
            map_one] <;> norm_num))
      | .hermiteH | .bernoulli => `(tactic| (rw [hP $qT] <;> norm_num))
    let valueTac ← `(tactic| (
      have hP : $identity := by $script:tactic
      $use:tactic))
    let (statement, finish) ← match outcome? with
      | none => pure (← `($lhs = $vT), ← `(tactic| exact hV))
      | some outcome => pure (← `($lhs = $vT ∧ $(← SpecialFunctions.boundsSyntax lhs outcome)),
          ← `(tactic| exact ⟨hV, by rw [hV] <;> norm_num⟩))
    Algebra.proveStatement family.name statement (← `(tactic| (
      have hV : $lhs = $vT := by $valueTac:tactic
      $finish:tactic)))
  let (output, outputType) := SpecialFunctions.valueOutput value digits outcome?
  logReport ref {
    domain := s!"{family.name} polynomial at a rational point"
    input := surfaceText input
    inputType := "scalar ℝ"
    output
    outputType
  } #[← liftTermElabM <| Algebra.checkedEvidence family.name
    (if outcome?.isSome then s!"Exact value and digits of {family.name} {n}"
      else s!"Exact value of {family.name} {n}") proposition proof]

end CAS.Command.OrthogonalPolynomials
