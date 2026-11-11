/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

import CAS
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import CASOracle.Integrate

/-!
# Floating-point answers of an oracle, enclosed and checked

An oracle's numbers are decimals computed in floating point. SymLean uses one only as the center
of a statement it then proves with exact rational arithmetic or with the certified interval
evaluation of `cega`, whose enclosures come from FloatLib's outward-rounded intervals and are
checked in the kernel. The tolerance is fixed by the command (`(digits := d)`, default 6), never
by the oracle, and the displayed center is the one in the theorem.

* `#cas [nsolve x in [a, b], oracle := o] (lhs = rhs)` (the interval may be omitted for a
  polynomial equation): for each root `r` the oracle reports, with `c` the decimal of `r` to
  `d` places, `∃ x ∈ Set.Icc a b, |x - c| ≤ 10⁻ᵈ ∧ lhs = rhs` (`∃ x, …` without an interval),
  from the intermediate value theorem (`intermediate_value_Icc`) on
  `[c - 10⁻ᵈ, c + 10⁻ᵈ] ∩ [a, b]`: continuity by `fun_prop`, and by `norm_num` or bare `cega`
  that `lhs - rhs` is at most `0` at one end and at least `0` at the other. A root at a rational
  point, such as an end of `[a, b]`, is certified at that point instead, where `norm_num`, `simp`,
  the points where `sin` and `cos` are `0`, `1` or `-1` (`Real.sin_eq_zero_iff`,
  `Real.cos_eq_one_iff` and the like) or `cas` prove `lhs = rhs`. Otherwise a root is refused
  when `lhs - rhs` has the same nonzero sign at both ends of its interval, as for a double root
  inside it. A center is certified once, however many roots
  the oracle reports there, as it reports a multiple root. The interval needs `a < b`. Existence
  only: that the root is simple, or that the list is complete, is a hint. The oracle finds the
  roots with its own numerics, which evaluate `log`, `sqrt`, real powers and quotients as complex
  functions, so it misses the roots that only Lean's conventions give, such as the zeros of
  `Real.sqrt (x - 1/3)` on `[0, 1/3]`.
* `#cas [nintegrate x in [a, b], oracle := o] f`: with `c` the oracle's value to `d` places,
  `|(∫ x in a..b, f x) - c| ≤ 10⁻ᵈ`, by the batch Simpson certificate of `#cas [nintegrate]`
  about `c` (interval enclosures of the fourth derivative, all panels checked in one kernel
  evaluation); a value that it does not certify is refused.
* `#cas [eigenvalues, oracle := o] A` for a square rational matrix literal: for each real
  eigenvalue the oracle reports, `∃ t ∈ Set.Icc (c - 10⁻ᵈ) (c + 10⁻ᵈ), t ∈ spectrum ℝ A`, from
  a sign change on that interval of the square-free part `S` of the characteristic polynomial
  `a = S G` (`CAS.Analysis.Matrix.exists_mem_spectrum_of_signChange`). The theorem
  `Matrix.charpoly A = ofCoeffList a` is proved once, and each interval costs one kernel
  evaluation of `S G = a` and of the signs of `S` at its ends. A multiple eigenvalue is a simple
  root of `S`, where `S` changes sign, so it can be certified like a simple one. Completeness is a
  hint.

* `#cas [enclose x in [a, b], y in [c, d], oracle := gappa] e`: the oracle's enclosure of `e` on
  the box, rounded outward to `d` places, as `∀ x y, a ≤ x → x ≤ b → … → lo ≤ e ∧ e ≤ hi`,
  proved by bare `cega` from the box hypotheses.

`nsolve` runs on `sympy`, `pari` and `flint` (the last two for polynomials); `nintegrate` on
`sympy`, `sage`, `pari` and `flint`; `eigenvalues` on `sympy`, `sage`, `pari` and `flint`;
`enclose` on `gappa` (for `+`, `-`, `*`, `/`, natural powers, `sqrt` and `|·|`).

## Implementation notes

The oracle's number only tells us where to look: we accept a proposal only when we prove the
statement built from it, and refuse it otherwise. That statement is an error bound, not a claim of
correct rounding: a root, an eigenvalue or the integral lies within `10⁻ᵈ` of the decimal `c`, which
may differ from the correctly rounded value by one unit in the last place, and `e` lies between the
oracle's bounds rounded outward. The proofs are classical and checked by Lean: the intermediate
value theorem for roots, the composite Simpson rule with an enclosed fourth derivative for integrals
(`NIntegrate.batchRoute`, the route of `#cas [nintegrate]` without an oracle), a sign change of the
square-free part of the characteristic polynomial for eigenvalues, and interval evaluation for
enclosures. A proposed integral more than `100 * 10⁻ᵈ` away from our own uncertified Simpson
estimate is refused before the certificate search.

The proposals come from the oracles' numerics. SymPy isolates the real roots of a polynomial exactly
before it evaluates them; for any other equation it evaluates `lhs - rhs` at 2001 equally spaced
points of the interval, both ends included, takes each point where it vanishes as a root (at an end,
a value below the working precision, which is how a root there rounds) and refines each sign change
between neighbouring points with mpmath's findroot, skipping points where the function is not real;
its numerical integrals run on mpmath. PARI/GP uses polrootsreal and intnum, the `flint` oracle
FLINT's ball arithmetic (Arb, cited in `CASOracle.Oracle`) for roots, integrals and eigenvalues, and
Sage the roots of the characteristic polynomial in a real field of the precision asked. For
eigenvalues FLINT computes the characteristic polynomial exactly and Arb isolates the roots of its
square-free factors, so that a repeated or defective eigenvalue is found like a simple one:
`acb_mat.eig` fails to isolate the eigenvalues of `!![2, 0, 0; 0, 2, 0; 0, 0, 3]`, even with
`multiple=True`. Gappa prints the bounds it proves for the expression on the box; we keep only these
bounds, round them outward and prove the enclosure again with `cega`. DSLean's own `gappa` tactic
rebuilds Gappa's Coq proof in Lean instead, and leaves to the user the steps its tactics do not
close; with `cega` no step is left open.

## References

* Guillaume Melquiond, *Gappa*, <https://gappa.gitlabpages.inria.fr/>. Tested with version
  1.4.2.
* Marc Daumas and Guillaume Melquiond, "Certification of bounds on expressions involving rounded
  operators", *ACM Transactions on Mathematical Software* 37 (2010), no. 1, pp. 1-20,
  <https://doi.org/10.1145/1644001.1644003>.
* The mpmath development team, *mpmath: a Python library for arbitrary-precision floating-point
  arithmetic*, <https://mpmath.org/>. Tested with version 1.3.0.
-/

namespace CASOracle.Numeric

open Lean Elab Command Meta Term
open CAS CAS.Command CAS.Command.InfoView
open CASOracle.Accept CASOracle.Wire CASOracle.Integrate

/-- The real term `(m : ℝ) / 10 ^ d` (or its negation) of the rational `m / 10 ^ d`, or the same
term in the field `field`. -/
def decimalTerm (m : Int) (d : Nat) (field : Name := ``Real) : MacroM Term := do
  let numerator : Term := ⟨Syntax.mkNumLit (toString m.natAbs)⟩
  let denominator : Term := ⟨Syntax.mkNumLit (toString (10 ^ d))⟩
  let K := mkIdent field
  if m < 0 then `((-(($numerator : $K) / $denominator))) else `((($numerator : $K) / $denominator))

/-- `m / 10 ^ d` written in decimals. -/
def renderScaled (m : Int) (d : Nat) : String :=
  let digits := Digits.renderDecimal m.natAbs d
  if m < 0 then "-" ++ digits else digits

/-- The nearest integer to `q`. -/
def roundRat (q : ℚ) : Int := ⌊q + 1 / 2⌋

/-- The centers `m` of the decimals `m / 10 ^ d` nearest to `values`, in order and each once: a
multiple root or eigenvalue that an oracle reports several times is certified once. -/
def centersOf (values : Array ℚ) (d : Nat) : Array Int :=
  values.foldl (init := #[]) fun centers value ↦
    let m := roundRat (value * 10 ^ d)
    if centers.contains m then centers else centers.push m

/-- The decimals of an oracle's answer, as rationals. -/
def decimals (values : Array String) : CoreM (Array ℚ) :=
  values.mapM fun text ↦ do
    let some q := parseDecimal? text | throwError "the oracle's number {text} is not a decimal"
    return q

/-- The Python arguments of a numerical task on the expression `f` in `v0`: SymPy text and
`v0` for SymPy and FLINT, GP text for PARI. -/
def numericArguments (oracle : Oracle) (f : Verified.Expr (Fin 1)) : TermElabM String := do
  let text ← Translate.write (Translate.requestLanguage oracle) wireName f
  if oracle == .pari then return py text
  return s!"{pyRead text ["v0"]}, *{pyVariables ["v0"]}"

/-- The option `(digits := d)` of the oracle form of `command`, between 1 and 12 and by default
6. -/
def digitsOf (command : String) (cfg : Syntax) : CommandElabM Nat := do
  let d ← parseDigitsOption command cfg 6
  unless d ≤ 12 do throwErrorAt cfg "{command} accepts between 1 and 12 digits"
  return d

/-! ## Roots -/

/-- `#cas [nsolve x in [a, b], oracle := o] (lhs = rhs)`. -/
syntax (name := casNSolveOracleCommand)
  "#cas" optConfig "[" &"nsolve" ident (" in " "[" term ", " term "]")?
    ", " &"oracle" " := " ident "]" term : command

/-- Whether Lean and the oracles may disagree about where `f` vanishes: the variable is inside a
logarithm, a square root, a real power, an inverse sine or cosine, or the denominator of a
quotient, whose values outside their domain Lean fixes by convention (`Real.sqrt x = 0` for
`x < 0`, `Real.log x = Real.log |x|`, `x / 0 = 0`) and SymPy evaluates as complex numbers or not
at all. A constant such as `1 / 3` is not such a case. -/
def conventional : Verified.Expr (Fin 1) → Bool
  | .log a | .sqrt a | .asin a | .acos a => Admission.hasVar a
  | .rpow a b => Admission.hasVar a || Admission.hasVar b
  | .div a b => Admission.hasVar b || conventional a
  | .add a b | .mul a b | .sub a b => conventional a || conventional b
  | .neg a | .pow a _ | .sin a | .cos a | .atan a | .exp a => conventional a
  | _ => false

/-- One certified root: the theorem that the equation has a solution within `10⁻ᵈ` of
`m / 10 ^ d`, inside the requested interval when there is one:
`∃ x ∈ Set.Icc a b, |x - c| ≤ 10⁻ᵈ ∧ lhs = rhs` (or `∃ x, …` without an interval). The center
and each end of `[a, b]` within `10⁻ᵈ` of it, where an uncertified evaluation finds the residual
`lhs - rhs` near zero, are tried first as the solution itself, with `lhs = rhs` proved there by
`norm_num`, `simp`, the points where `sin` and `cos` are `0`, `1` or `-1`, or `cas`; this
certifies a zero at an end of
`[a, b]` and needs no continuity.
Otherwise the intermediate value theorem runs on `[c - 10⁻ᵈ, c + 10⁻ᵈ] ∩ [a, b]`; the direction
of the sign change comes from an uncertified evaluation and only selects the proof. -/
def certifyRoot (x : TSyntax `ident) (lhs rhs : Verified.Expr (Fin 1)) (m : Int) (d : Nat)
    (interval : Option (ℚ × ℚ)) : TermElabM (Option (Lean.Expr × Lean.Expr)) := do
  let var : Fin 1 → Term := fun _ ↦ x
  let lhsT ← liftMacroM <| toTerm var lhs
  let rhsT ← liftMacroM <| toTerm var rhs
  let center : ℚ := (m : ℚ) / 10 ^ d
  let delta : ℚ := 1 / 10 ^ d
  let (loQ, hiQ) := match interval with
    | some (a, b) => (max (center - delta) a, min (center + delta) b)
    | none => (center - delta, center + delta)
  unless loQ < hiQ do return none
  let real (q : ℚ) : TermElabM Term := do `(($(← ratSyntax q) : ℝ))
  let lo ← real loQ
  let hi ← real hiQ
  let c ← liftMacroM <| decimalTerm m d
  let δ ← liftMacroM <| decimalTerm 1 d
  let residual : Verified.Expr (Fin 1) := .sub lhs rhs
  let close ← `(abs_sub_le_iff.mpr ⟨by linarith [hy.2], by linarith [hy.1]⟩)
  let (statement, finish) ← match interval with
    | some (a, b) => do
        let a ← real a
        let b ← real b
        pure (← `(∃ $x:ident ∈ Set.Icc $a $b, |$x - $c| ≤ $δ ∧ $lhsT = $rhsT),
          ← `(tactic| exact ⟨y, ⟨by linarith [hy.1], by linarith [hy.2]⟩, $close,
            sub_eq_zero.mp hfy⟩))
    | none => do
        pure (← `(∃ $x:ident : ℝ, |$x - $c| ≤ $δ ∧ $lhsT = $rhsT),
          ← `(tactic| exact ⟨y, $close, sub_eq_zero.mp hfy⟩))
  let ends := match interval with
    | some (a, b) => [a, b]
    | none => []
  let near (w : ℚ) : Bool := match NIntegrate.sample residual w with
    | some value => decide (|value| ≤ 1 / 10 ^ (d + 4))
    | none => true
  let witnesses := ((center :: ends).filter fun w ↦
    decide (loQ ≤ w) && decide (w ≤ hiQ) && near w).eraseDups
  -- `sin g` or `cos g` equal to `0`, `1` or `-1` at `w`, where `g w` is the matching multiple of
  -- `π / 2`: Mathlib's `Real.sin_eq_zero_iff`, `Real.cos_eq_one_iff` and the like, with the
  -- integer that an uncertified evaluation finds, which `ring` then checks.
  let periodic (w : ℚ) : TermElabM (List (TSyntax `tactic)) := do
    let pi : ℚ := 314159265358979323846 / 10 ^ 20
    let integer (q : ℚ) : TermElabM (Option Term) := do
      let n := roundRat q
      unless |q - n| ≤ 1 / 10 ^ 6 do return none
      let literal : Term := ⟨Syntax.mkNumLit (toString n.natAbs)⟩
      some <$> if n < 0 then `((-($literal : ℤ))) else `(($literal : ℤ))
    let value? : Verified.Expr (Fin 1) → Option ℤ
      | .nat n => some n
      | .int n => some n
      | .neg (.nat n) => some (-(n : ℤ))
      | _ => none
    -- The integer `k` with `g w / π = offset + period k`, the one of the lemma `iff`.
    let closer (g : Verified.Expr (Fin 1)) (offset : ℚ) (period : ℚ) (iff : Name) :
        TermElabM (List (TSyntax `tactic)) := do
      let some turns := (NIntegrate.sample g w).map (· / pi) | return []
      let some k ← integer ((turns - offset) / period) | return []
      return [← `(tactic| (rw [$(mkIdent iff):ident]; exact ⟨$k, by push_cast; ring⟩))]
    let some c := value? rhs | return []
    match lhs with
    | .sin g =>
        if c == 0 then closer g 0 1 ``Real.sin_eq_zero_iff
        else if c == 1 then closer g (1 / 2) 2 ``Real.sin_eq_one_iff
        else if c == -1 then closer g (-1 / 2) 2 ``Real.sin_eq_neg_one_iff
        else return []
    | .cos g =>
        if c == 0 then closer g (1 / 2) 1 ``Real.cos_eq_zero_iff
        else if c == 1 then closer g 0 2 ``Real.cos_eq_one_iff
        else if c == -1 then closer g 1 2 ``Real.cos_eq_neg_one_iff
        else return []
    | _ => return []
  let mut direct : List Term := []
  for w in witnesses do
    let wT ← real w
    let closers := [← `(tactic| norm_num), ← `(tactic| (ring_nf; simp))] ++ (← periodic w) ++
      [← `(tactic| cas)]
    for closer in closers do
      let distance ← `(by rw [abs_le]; constructor <;> norm_num)
      let value ← `(by $closer:tactic)
      let proof ← match interval with
        | some _ => `(⟨$wT, ⟨by norm_num, by norm_num⟩, $distance, $value⟩)
        | none => `(⟨$wT, $distance, $value⟩)
      direct := direct ++ [proof]
  if let some result ← firstProved "nsolve" statement direct then return some result
  let some fLo := NIntegrate.sample residual loQ | return none
  let some fHi := NIntegrate.sample residual hiQ | return none
  let increasing ← if fLo ≤ 0 ∧ 0 ≤ fHi then pure true
    else if 0 ≤ fLo ∧ fHi ≤ 0 then pure false
    else return none
  let f ← `(fun $x:ident : ℝ ↦ $lhsT - $rhsT)
  let continuityProofs : List Term :=
    [← `((by fun_prop : Continuous $f).continuousOn), ← `((by fun_prop))]
  let signClosers : List (TSyntax `tactic) := [← `(tactic| norm_num), ← `(tactic| cega)]
  let mut proofs : List Term := []
  for continuity in continuityProofs do
    for closer in signClosers do
      let proof ← if increasing then
          `(by
            have hcont : ContinuousOn $f (Set.Icc $lo $hi) := $continuity
            have hlo : $f $lo ≤ 0 := by beta_reduce; $closer:tactic
            have hhi : 0 ≤ $f $hi := by beta_reduce; $closer:tactic
            obtain ⟨y, hy, hfy⟩ := intermediate_value_Icc (by norm_num) hcont ⟨hlo, hhi⟩
            $finish:tactic)
        else
          `(by
            have hcont : ContinuousOn $f (Set.Icc $lo $hi) := $continuity
            have hlo : 0 ≤ $f $lo := by beta_reduce; $closer:tactic
            have hhi : $f $hi ≤ 0 := by beta_reduce; $closer:tactic
            obtain ⟨y, hy, hfy⟩ := intermediate_value_Icc' (by norm_num) hcont ⟨hhi, hlo⟩
            $finish:tactic)
      proofs := proofs ++ [proof]
  firstProved "nsolve" statement proofs

/-- Elaborates `#cas [nsolve x in [a, b], oracle := o] (lhs = rhs)`: the oracle's roots, each
enclosure proved in Lean before it is reported. -/
@[command_elab casNSolveOracleCommand]
def elabNSolve : CommandElab := fun stx ↦ do
  let `(#cas $cfg:optConfig [nsolve $x:ident $[in [$a?:term, $b?:term]]?,
      oracle := $o:ident] $input:term) := stx | throwUnsupportedSyntax
  let oracle ← liftCoreM (oracleOf o)
  let d ← digitsOf "nsolve" cfg
  let equation : Term := ⟨SpecialFunctions.unparen input⟩
  let `($l = $r) := equation | throwErrorAt input "nsolve: write the equation as `lhs = rhs`"
  let parseSide (side : Term) : CommandElabM (Verified.Expr (Fin 1)) := do
    match ← parseExact side [x.getId] with
    | ⟨[_], expression, _⟩ => pure expression
    | _ => throwErrorAt side "nsolve: the equation must be in {x.getId} alone"
  let lhs ← parseSide l
  let rhs ← parseSide r
  let interval ← match a?, b? with
    | some a, some b => pure (some (← SpecialFunctions.parseRational "nsolve" a,
        ← SpecialFunctions.parseRational "nsolve" b))
    | _, _ => pure none
  if let some (a, b) := interval then
    unless a < b do throwErrorAt stx "nsolve needs rational limits a < b"
  let bounds := match interval with
    | some (a, b) => s!", {py (ratText a)}, {py (ratText b)}"
    | none => ""
  let found ← liftTermElabM do
    askPython oracle "nroots" ["root"]
      s!"{← numericArguments oracle (Verified.Expr.sub lhs rhs)}, {d + 4}{bounds}"
      (allowEmpty := true)
  let roots ← liftCoreM <| decimals (← liftCoreM <| payloads oracle found "root" 100)
  if roots.isEmpty then
    let caveat := if conventional (.sub lhs rhs) then
        s!"; {oracle.name} evaluates log, sqrt, powers and quotients as complex functions or \
          not at all where Lean's are fixed by convention, as Real.sqrt x = 0 for x < 0, so it \
          can miss such roots"
      else ""
    throwErrorAt input "nsolve: {oracle.name} reports no real root (which proves nothing){caveat}"
  withAuditedEvidence "nsolve" do
    let mut steps := #[]
    let mut shown := #[]
    let mut refused := #[]
    for m in centersOf roots d do
      match ← liftTermElabM (certifyRoot x lhs rhs m d interval) with
      | some (proposition, proof) =>
          steps := steps.push (s!"A root within 10^-{d} of {renderScaled m d}", proposition,
            proof)
          shown := shown.push s!"{renderScaled m d} ± 10^-{d}"
      | none =>
          let center : ℚ := (m : ℚ) / 10 ^ d
          let atEnd := match interval with
            | some (a, b) => decide (center - 1 / 10 ^ d ≤ a) || decide (b ≤ center + 1 / 10 ^ d)
            | none => false
          refused := refused.push (renderScaled m d, atEnd)
    if steps.isEmpty then
      throwErrorAt input "nsolve: no root proposed by {oracle.name} could be certified \
        (refused: {(refused.map (·.1)).toList})"
    let report ← liftTermElabM <| evidence steps
    let hints := #[m!"the roots listed are all the real roots \
      {match interval with | some (a, b) => s!"in [{a}, {b}]" | none => ""}",
      m!"each root is simple and the only one in its interval"] ++
      refused.map fun (center, atEnd) ↦ if atEnd then
          m!"{center}: at an end of the interval, where the value could not be proved zero, and \
            no sign change; not certified"
        else m!"{center}: no sign change on its interval, not certified"
    logReport input {
      domain := match interval with
        | some (a, b) => s!"{x.getId} ∈ [{a}, {b}]"
        | none => s!"{x.getId} ∈ ℝ"
      input := surfaceText input.raw
      inputType := "equation in ℝ"
      output := ", ".intercalate shown.toList
      outputType := "a root in each interval (existence checked)"
    } #[hintsNode oracle hints, report]

/-! ## Integrals -/

/-- `#cas [nintegrate x in [a, b], oracle := o] f`. -/
syntax (name := casNIntegrateOracleCommand)
  "#cas" optConfig "[" &"nintegrate" ident " in " "[" term ", " term "]"
    ", " &"oracle" " := " ident "]" term : command

/-- Elaborates `#cas [nintegrate x in [a, b], oracle := o] f`: an enclosure of the integral from
the oracle's estimate, proved in Lean before it is reported. -/
@[command_elab casNIntegrateOracleCommand]
def elabNIntegrate : CommandElab := fun stx ↦ do
  let `(#cas $cfg:optConfig [nintegrate $x:ident in [$aStx:term, $bStx:term],
      oracle := $o:ident] $input:term) := stx | throwUnsupportedSyntax
  let oracle ← liftCoreM (oracleOf o)
  let d ← digitsOf "nintegrate" cfg
  let a ← SpecialFunctions.parseRational "nintegrate" aStx
  let b ← SpecialFunctions.parseRational "nintegrate" bStx
  unless a < b do throwErrorAt stx "nintegrate needs rational limits a < b"
  let f : Verified.Expr (Fin 1) ← match ← parseExact input [x.getId] with
    | ⟨[_], expression, _⟩ => pure expression
    | _ => throwErrorAt input "nintegrate: the integrand must be in {x.getId} alone"
  let found ← liftTermElabM do
    let arguments ← numericArguments oracle f
    let arguments := if oracle == .pari then s!"{arguments}, \"v0\"" else arguments
    askPython oracle "nintegrate" ["value"]
      s!"{arguments}, {py (ratText a)}, {py (ratText b)}, {d + 4}"
  let text ← liftCoreM <| payload oracle found "value"
  let some value := parseDecimal? text | throwError "the oracle's value {text} is not a decimal"
  let m := roundRat (value * 10 ^ d)
  let body ← liftMacroM <| toTerm (fun _ ↦ x) f
  let c ← liftMacroM <| decimalTerm m d
  let epsilon ← liftMacroM <| decimalTerm 1 d
  let aT ← ratSyntax a
  let bT ← ratSyntax b
  let statement ← `(|(∫ $x:ident in ($aT : ℝ)..($bT : ℝ), $body) - $c| ≤ $epsilon)
  let tolerance : ℚ := 1 / 10 ^ d
  -- A screen for refusals only: a value far from SymLean's own uncertified estimate cannot be
  -- certified, so it is refused before the certificate search.
  if let some estimate := NIntegrate.simpson f a b 512 then
    if |estimate - (m : ℚ) / 10 ^ d| > 100 * tolerance then
      throwErrorAt input "nintegrate: the value {renderScaled m d} proposed by {oracle.name} \
        could not be certified: it is far from the Simpson estimate \
        {renderScaled (roundRat (estimate * 10 ^ d)) d}"
  withAuditedEvidence "nintegrate" do
    -- The batch Simpson certificate of `#cas [nintegrate]` about the proposed value: one kernel
    -- evaluation checks all panels, the fourth derivative enclosed by interval evaluation. Its
    -- statement is matched against the one built here.
    let budget := max (maxHeartbeats.get (← getOptions)) 1000000
    let batch ← liftTermElabM <| withTheReader Core.Context (fun context ↦
        { context with maxHeartbeats := budget * 1000 }) <| withCurrHeartbeats do
      try
        match ← NIntegrate.batchRoute d f a b (some ((m : ℚ) / 10 ^ d)) with
        | none => pure none
        | some (_, panels, certificate) =>
            let certificate ← Term.exprToSyntax certificate
            let attempt ← firstProved "nintegrate" statement
              [← `(by exact $certificate), ← `(by simpa using $certificate),
                ← `(by convert ($certificate) using 2 <;> norm_num)]
            pure (attempt.map fun (proposition, proof) ↦ (panels, proposition, proof))
      catch _ => pure none
    let some (panels, proposition, proof) := batch
      | throwErrorAt input "nintegrate: the value {renderScaled m d} proposed by \
          {oracle.name} could not be certified to {d} decimals (it may be wrong, 1024 Simpson \
          panels may not fix the decimals, or the integrand may have no fourth-derivative \
          validity certificate on [{a}, {b}])"
    let route := s!"batch Simpson certificate with {panels} panels"
    let report ← liftTermElabM <| evidence
      #[(s!"The integral is within 10^-{d} of the value proposed by {oracle.name}",
        proposition, proof)]
    logReport input {
      domain := s!"{x.getId} ∈ [{a}, {b}]"
      input := surfaceText input.raw
      inputType := "scalar ℝ"
      output := s!"{renderScaled m d} ± 10^-{d}"
      outputType := "certified value of the integral"
    } #[computationNode "Certified quadrature" #[
        m!"Value proposed by {oracle.name}: {text} (not proof)",
        m!"Proof: {route}"],
      report]

/-! ## Eigenvalues -/

/-- `#cas [eigenvalues, oracle := o] A`. -/
syntax (name := casEigenvaluesOracleCommand)
  "#cas" optConfig "[" &"eigenvalues" ", " &"oracle" " := " ident "]" term : command

/-- The theorem `∃ t ∈ Set.Icc ((m - 1) / 10 ^ d) ((m + 1) / 10 ^ d), t ∈ spectrum ℝ M` for the
real matrix literal `M` of `A` and each center `m` of `ms` around which the square-free part `S`
of the characteristic polynomial `a = S G` changes sign, with its proof, and the centers without
a sign change. The theorems `Matrix.charpoly A = ofCoeffList a` and `A.map (↑) = M` are proved
once, as auxiliary lemmas; each interval then costs one kernel evaluation of `S G = a` and of the
signs of `S` at its ends (`CAS.Analysis.Matrix.exists_mem_spectrum_of_signChange`). -/
def certifyEigenvalues (A : LinearAlgebra.QMatrix) (matrix : Term) (ms : Array Int) (d : Nat) :
    TermElabM (Array (Int × Lean.Expr × Lean.Expr) × Array Int) := do
  let n := A.rows
  let a := A.charpoly
  let S := Algebra.Dense.monic
    (Algebra.Dense.divMod a (Algebra.Dense.gcd a (Algebra.Dense.derivative a))).1
  let G := (Algebra.Dense.divMod a S).1
  let interval (m : Int) : ℚ × ℚ := (((m - 1 : Int) : ℚ) / 10 ^ d, ((m + 1 : Int) : ℚ) / 10 ^ d)
  let (passing, refused) := ms.partition fun m ↦
    let (lo, hi) := interval m
    decide (Algebra.Dense.eval S lo * Algebra.Dense.eval S hi < 0)
  if passing.isEmpty then return (#[], refused)
  let elabList (p : Algebra.Dense) : TermElabM Lean.Expr := do
    let e ← elabTerm (← LinearAlgebra.coeffsTerm p.toList) none
    synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  -- The ends `(m ∓ 1) / 10 ^ d` in the rationals, written as in the statement, so that the casts
  -- to `ℝ` give its ends.
  let elabEnd (m : Int) : TermElabM Lean.Expr := do
    let e ← elabTerm (← liftMacroM <| decimalTerm m d ``Rat) none
    synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  let At ← LinearAlgebra.matrixTerm A n n
  let castRows ← A.mapM fun row ↦ do
    `(![$(← row.mapM fun q ↦ do `((($(← ratSyntax q) : ℚ) : ℝ))),*])
  let castM ← `(![$castRows,*])
  let (hAType, hAProof) ← proveStatement "eigenvalues"
    (← `(Matrix.charpoly $At = Polynomial.ofCoeffList $(← LinearAlgebra.coeffsTerm a.toList)))
    (← `(by $(← LinearAlgebra.charpolyTactic A none true):tactic))
  let (hMType, hMProof) ← proveStatement "eigenvalues"
    (← `(Matrix.map $At ((↑) : ℚ → ℝ) = $matrix))
    (← `(by
      rw [CAS.Analysis.Matrix.map_of_eq]
      change Matrix.of $castM = _
      norm_num))
  let hA := Lean.mkConst (← CAS.Tactic.ProofCarrier.mkKernelAuxLemma [] hAType hAProof `_proof)
  let hM := Lean.mkConst (← CAS.Tactic.ProofCarrier.mkKernelAuxLemma [] hMType hMProof `_proof)
  -- `A`, `M` and `a` as they occur in the two lemmas.
  let AE := (hAType.getArg! 1).appArg!
  let ME := hMType.appArg!
  let aE := hAType.appArg!.appArg!
  let SE ← elabList S
  let GE ← elabList G
  let mut certified : Array (Int × Lean.Expr × Lean.Expr) := #[]
  for m in passing do
    let raw ← Command.Matrix.certify "eigenvalues"
      ``CAS.Analysis.Matrix.exists_mem_spectrum_of_signChange
      #[AE, ME, aE, SE, GE, ← elabEnd (m - 1), ← elabEnd (m + 1), hA, hM]
    let rawT ← exprToSyntax raw
    let t := mkIdent `t
    let statement ← `(∃ $t:ident ∈ Set.Icc $(← liftMacroM <| decimalTerm (m - 1) d)
      $(← liftMacroM <| decimalTerm (m + 1) d), $t ∈ spectrum ℝ $matrix)
    let (proposition, proof) ← proveStatement "eigenvalues" statement
      (← `(by first | exact_mod_cast $rawT | (have h := $rawT; norm_num at h ⊢; exact h)))
    certified := certified.push (m, proposition, proof)
  return (certified, refused)

/-- Elaborates `#cas [eigenvalues, oracle := o] A`: the oracle's real eigenvalues, each enclosure
proved in Lean before it is reported. -/
@[command_elab casEigenvaluesOracleCommand]
def elabEigenvalues : CommandElab := fun stx ↦ do
  let `(#cas $cfg:optConfig [eigenvalues, oracle := $o:ident] $input:term) := stx
    | throwUnsupportedSyntax
  let oracle ← liftCoreM (oracleOf o)
  let d ← digitsOf "eigenvalues" cfg
  let A ← LinearAlgebra.parseQMatrix input
  unless A.rows = A.cols do throwErrorAt input "eigenvalues: the matrix must be square"
  let matrix ← LinearAlgebra.matrixTermOver A (← `(ℝ))
  let rows := "[" ++ ", ".intercalate (A.toList.map fun row ↦
    pyList (row.toList.map ratText)) ++ "]"
  let found ← liftCoreM <|
    askPython oracle "eigenvalues" ["eigenvalue"] s!"{rows}, {d + 4}" (allowEmpty := true)
  let values ← liftCoreM <| decimals (← liftCoreM <| payloads oracle found "eigenvalue" 100)
  if values.isEmpty then
    throwErrorAt input "eigenvalues: {oracle.name} reports no real eigenvalue (which proves \
      nothing)"
  withAuditedEvidence "eigenvalues" do
    let centers := centersOf values d
    let (certified, refused) ← liftTermElabM (certifyEigenvalues A matrix centers d)
    let refused := refused.map (renderScaled · d)
    -- Values that round to one center: eigenvalues closer than the tolerance, or one reported
    -- twice, where the sign of the square-free part need not change.
    let close := if values.size > centers.size then
        s!"; eigenvalues within 10^-{d} of each other share an interval, where the sign need \
          not change, and more digits, as in (digits := {d + 2}), separate them"
      else ""
    if certified.isEmpty then
      throwErrorAt input "eigenvalues: no eigenvalue proposed by {oracle.name} could be \
        certified (refused: {refused.toList}){close}"
    let steps := certified.map fun (m, proposition, proof) ↦
      (s!"An eigenvalue within 10^-{d} of {renderScaled m d}", proposition, proof)
    let shown := certified.toList.map fun (m, _) ↦ s!"{renderScaled m d} ± 10^-{d}"
    let report ← liftTermElabM <| evidence steps
    logReport input {
      domain := "ℝ"
      input := surfaceText input.raw
      inputType := s!"{A.rows} × {A.rows} rational matrix"
      output := ", ".intercalate shown
      outputType := "a real eigenvalue in each interval (existence checked)"
    } #[hintsNode oracle (#[m!"these are all the real eigenvalues"] ++
        refused.map (m!"{·}: no sign change of the square-free part of the characteristic \
          polynomial, not certified{close}")),
      report]

/-! ## Enclosures -/

/-- `#cas [enclose x in [a, b], y in [c, d], oracle := o] e`. -/
syntax (name := casEncloseOracleCommand)
  "#cas" optConfig "[" &"enclose" ident " in " "[" term ", " term "]"
    (atomic(", " ident " in ") "[" term ", " term "]")* ", " &"oracle" " := " ident "]" term :
    command

/-- Elaborates `#cas [enclose x in [a, b], …, oracle := o] e`: an enclosure of the range of `e`
from the oracle's estimate, proved in Lean before it is reported. -/
@[command_elab casEncloseOracleCommand]
def elabEnclose : CommandElab := fun stx ↦ do
  let `(#cas $cfg:optConfig [enclose $x:ident in [$a:term, $b:term]
      $[, $ys:ident in [$cs:term, $ds:term]]*, oracle := $o:ident] $input:term) := stx
    | throwUnsupportedSyntax
  let oracle ← liftCoreM (oracleOf o)
  let d ← digitsOf "enclose" cfg
  let coordinates := #[x] ++ ys
  let names := coordinates.toList.map (·.getId)
  let n := names.length
  let lowers ← (#[a] ++ cs).mapM fun t ↦ SpecialFunctions.parseRational "enclose" t
  let uppers ← (#[b] ++ ds).mapM fun t ↦ SpecialFunctions.parseRational "enclose" t
  unless (lowers.zip uppers).all (fun (l, u) ↦ l ≤ u) do
    throwErrorAt stx "enclose: every interval needs lower ≤ upper"
  let reified ← parseExact input names
  let expression : Verified.Expr (Fin n) ←
    if h : reified.names.length = n then pure (h ▸ reified.expr)
    else throwErrorAt input "enclose: unexpected coordinates"
  let (lo, hi, loText, hiText) ← liftTermElabM do
    requireTask oracle "enclose"
    let problem ← Translate.gappaProblem wireName
      (fun i ↦ (lowers[i.val]!, uppers[i.val]!)) expression
    -- Gappa writes its results on the standard error.
    let result ← run oracle #[] problem (maxErrorBytes := 1024 * 1024)
    if result.stderrTruncated then
      fail oracle (.failed "the answer is over 1048576 bytes")
    let output := result.stdout ++ "\n" ++ result.stderr
    let some (lo, hi) := Translate.gappaBounds? output
      | fail oracle (.unsupported s!"Gappa proved no enclosure: \
          {(output.trimAscii.toString.takeEnd 300).toString}")
    unless result.exitCode == 0 do
      fail oracle (.failed s!"the oracle exited with code {result.exitCode} after answering")
    return (lo, hi, ratText lo, ratText hi)
  -- The bounds, rounded outward to `d` decimals: a weaker claim with a readable statement.
  let loM : Int := ⌊lo * 10 ^ d⌋
  let hiM : Int := ⌈hi * 10 ^ d⌉
  let loT ← `(($(← ratSyntax ((loM : ℚ) / 10 ^ d)) : ℝ))
  let hiT ← `(($(← ratSyntax ((hiM : ℚ) / 10 ^ d)) : ℝ))
  let body ← liftMacroM <| toTerm (fun i ↦ coordinates[i.val]!) expression
  let mut statement ← `($loT ≤ $body ∧ $body ≤ $hiT)
  for i in (List.range n).reverse do
    let v := coordinates[i]!
    let lower ← ratSyntax lowers[i]!
    let upper ← ratSyntax uppers[i]!
    statement ← `($lower ≤ $v → $v ≤ $upper → $statement)
  statement ← `(∀ $coordinates* : ℝ, $statement)
  let hypotheses := (List.range (2 * n)).toArray.map fun i ↦ mkIdent (Name.mkSimple s!"h{i}")
  let proof ← `(by
    intro $(coordinates ++ hypotheses)*
    refine ⟨?_, ?_⟩ <;> cega)
  withAuditedEvidence "enclose" do
    let some (proposition, proof) ← liftTermElabM <| tryProve "enclose" statement proof
      | throwErrorAt input "enclose: the enclosure [{renderScaled loM d}, \
          {renderScaled hiM d}] proposed by {oracle.name} could not be certified by cega"
    let report ← liftTermElabM <| evidence
      #[(s!"The enclosure proposed by {oracle.name}, rounded outward", proposition, proof)]
    logReport input {
      domain := ", ".intercalate <| (List.range n).map fun i ↦
        s!"{names[i]!} ∈ [{lowers[i]!}, {uppers[i]!}]"
      input := surfaceText input.raw
      inputType := "scalar ℝ"
      output := s!"[{renderScaled loM d}, {renderScaled hiM d}]"
      outputType := "enclosure on the box, checked by cega"
    } #[computationNode s!"Enclosure proposed by {oracle.name} (not proof)"
        #[m!"[{loText}, {hiText}]"], report]

end CASOracle.Numeric
