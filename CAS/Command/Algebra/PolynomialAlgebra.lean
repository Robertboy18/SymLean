/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.Algebra.Basic

/-!
# Polynomial algebra in `ℚ[X]`: gcd, lcm, division, interpolation

The commands read their polynomials in one variable `x` as elements of Mathlib's `ℚ[X]` (the
variable becomes `Polynomial.X`) and prove statements about Mathlib's operations:

* `#cas [polynomialGCD] (p, q)` proves `gcd p q = g` for the normalized gcd of the
  `NormalizedGCDMonoid` `ℚ[X]`, which is monic;
* `#cas [polynomialLCM] (p, q)` proves `lcm p q = l` for the normalized lcm, also monic;
* `#cas [polynomialQuotientRemainder] (p, q)` proves `p / q = s ∧ p % q = r` for the Euclidean
  division of `ℚ[X]`; `[polynomialQuotient]` and `[polynomialRemainder]` print one part;
* `#cas [interpolatingPolynomial x] [(a₀, b₀), …]` (or `[b₁, b₂, …]` at `x = 1, 2, …`) proves
  `P.eval aᵢ = bᵢ` for every point and `P.natDegree ≤ n - 1`, which makes `P` unique.

## Implementation notes

The values come from the dense arithmetic of `CAS/Command/Algebra/Dense.lean` and are only
proposed: each statement is proved by a tactic script, and the kernel checks the proof as an
auxiliary theorem (`checkedEvidence`). For the gcd, `Dense.xgcd` gives the Bézout coefficients
`s`, `t` of the extended Euclidean algorithm, and `gcdProof` uses them as a certificate: `g`
divides `p` and `q` with explicit cofactors and `s p + t q = g`, so `gcd p q` and `g` divide each
other (`gcd_eq_normalize`), and `g` is monic (`Polynomial.Monic.normalize_eq_self`). The kernel
thus checks three polynomial identities and a monicity, however long the remainder sequence was.
`lcmProof` derives the lcm from `p ∣ l`, `q ∣ l`, the gcd and `gcd_mul_lcm`, and `divisionProof`
divides by the monic `q / lc q` and concludes by `Polynomial.div_modByMonic_unique`,
`Polynomial.div_def` and `Polynomial.mod_def`.

`interpolate` is Lagrange's formula, and its values and degree are checked by `norm_num` and
`compute_degree`. Polynomial identities in `ℚ[X]` are proved by evaluation (`Polynomial.funext`
over the infinite field `ℚ`) and `ring1`, degrees by `compute_degree`, monicity by `monicity`.
-/

public meta section

namespace CAS.Command.Algebra

open Lean Elab Command Meta Term
open CAS.Command.InfoView
open CAS.Verified.Expr.Alg

/-- The tactic proving that a polynomial of `ℚ[X]` is monic. -/
def monicTactic : TermElabM (TSyntax `tactic) :=
  `(tactic| first | monicity! | exact Polynomial.monic_one | monicity)

/-- The gcd `g` of `p` and `q` and a tactic proving `gcd P Q = G` for terms `P`, `Q` denoting
`p`, `q`. -/
def gcdProof (P Q : TSyntax `term) (p q : Dense) :
    TermElabM (Dense × TSyntax `term × TSyntax `tactic) := do
  let (g, s, t) := Dense.xgcd p q
  let G ← qPolyTerm g
  let U ← qPolyTerm (Dense.divMod p g).1
  let V ← qPolyTerm (Dense.divMod q g).1
  let S ← qPolyTerm s
  let T ← qPolyTerm t
  let identity ← polynomialIdentityTactic
  let monic ← monicTactic
  let script ← `(tactic| (
    have hp : ($G) ∣ ($P) := ⟨$U, by $identity:tactic⟩
    have hq : ($G) ∣ ($Q) := ⟨$V, by $identity:tactic⟩
    have hb : ($S) * ($P) + ($T) * ($Q) = ($G) := by $identity:tactic
    have hm : Polynomial.Monic ($G) := by $monic:tactic
    have hg : gcd ($P) ($Q) ∣ ($S) * ($P) + ($T) * ($Q) :=
      dvd_add (dvd_mul_of_dvd_right (gcd_dvd_left _ _) _)
        (dvd_mul_of_dvd_right (gcd_dvd_right _ _) _)
    rw [hb] at hg
    rw [gcd_eq_normalize hg (dvd_gcd hp hq), hm.normalize_eq_self]))
  return (g, G, script)

/-- The lcm `l` of `p` and `q` and a tactic proving `lcm P Q = L`. -/
def lcmProof (P Q : TSyntax `term) (p q : Dense) :
    TermElabM (Dense × TSyntax `term × TSyntax `tactic) := do
  let (g, G, gcdScript) ← gcdProof P Q p q
  let l := Dense.monic (Dense.divMod (Dense.mul p q) g).1
  let L ← qPolyTerm l
  let A ← qPolyTerm (Dense.divMod l p).1
  let B ← qPolyTerm (Dense.divMod l q).1
  -- `p q = g l c` for the constant `c = lead p * lead q`.
  let c := Dense.lead p * Dense.lead q
  let identity ← polynomialIdentityTactic
  let monic ← monicTactic
  let cT ← `(Polynomial.C (($(← ratSyntax c)) : ℚ))
  let script ← `(tactic| (
    have hp : ($P) ∣ ($L) := ⟨$A, by $identity:tactic⟩
    have hq : ($Q) ∣ ($L) := ⟨$B, by $identity:tactic⟩
    have hgcd : gcd ($P) ($Q) = ($G) := by $gcdScript:tactic
    have hmG : Polynomial.Monic ($G) := by $monic:tactic
    have hmL : Polynomial.Monic ($L) := by $monic:tactic
    have h1 : ($G) * ($L) ∣ ($P) * ($Q) := ⟨$cT, by $identity:tactic⟩
    have h2 : ($P) * ($Q) ∣ ($G) * lcm ($P) ($Q) := by
      rw [← hgcd]
      exact (gcd_mul_lcm ($P) ($Q)).symm.dvd
    have hl : ($L) ∣ lcm ($P) ($Q) := (mul_dvd_mul_iff_left hmG.ne_zero).mp (h1.trans h2)
    rw [lcm_eq_normalize (lcm_dvd hp hq) hl, hmL.normalize_eq_self]))
  return (l, L, script)

/-- The quotient `s` and remainder `r` of `p` by a nonzero `q` and a tactic proving
`P / Q = S ∧ P % Q = R`. -/
def divisionProof (P Q : TSyntax `term) (p q : Dense) :
    TermElabM (Dense × Dense × TSyntax `term × TSyntax `term × TSyntax `tactic) := do
  let c := Dense.lead q
  let qm := Dense.monic q
  let (sm, r) := Dense.divMod p qm
  let s := Dense.scale (1 / c) sm
  let Qm ← qPolyTerm qm
  let Sm ← qPolyTerm sm
  let S ← qPolyTerm s
  let R ← qPolyTerm r
  let cT ← `((($(← ratSyntax c)) : ℚ))
  let identity ← polynomialIdentityTactic
  let monic ← monicTactic
  let degree ← if Dense.isZero r then
      `(term| by
        rw [Polynomial.degree_zero]
        exact WithBot.bot_lt_iff_ne_bot.mpr
          (by rw [Ne, Polynomial.degree_eq_bot]; exact hm.ne_zero))
    else
      `(term| by
        apply Polynomial.degree_lt_degree
        rw [show Polynomial.natDegree ($R) = $(natTerm (Dense.degree r)) by compute_degree!,
          show Polynomial.natDegree ($Qm) = $(natTerm (Dense.degree qm)) by compute_degree!]
        norm_num)
  let script ← `(tactic| (
    have hm : Polynomial.Monic ($Qm) := by $monic:tactic
    have hq : ($Q) = Polynomial.C ($cT) * ($Qm) := by $identity:tactic
    have hlc : Polynomial.leadingCoeff ($Q) = $cT := by
      rw [hq, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hm.leadingCoeff, mul_one]
    have hnorm : ($Q) * Polynomial.C ($cT)⁻¹ = $Qm := by $identity:tactic
    have hu := Polynomial.div_modByMonic_unique (f := $P) ($Sm) ($R) hm
      ⟨by $identity:tactic, $degree⟩
    rw [Polynomial.div_def, Polynomial.mod_def, hlc, hnorm, hu.1, hu.2]
    exact ⟨by $identity:tactic, rfl⟩))
  return (s, r, S, R, script)

/-- Read a polynomial in at most the one variable `x`. -/
def denseOf (operation : String) (stx : Syntax) (x : Name) :
    CommandElabM (ReifiedExpr × Dense) := do
  let reified ← parseWithLeading stx [x]
  if h : reified.names.length = 1 then
    let rational ← match rationalOfExpr reified.expr with
      | .ok r => pure r
      | .error message => throwErrorAt stx "{operation}: {message}"
    unless rational.value.isPoly && rational.divisors.isEmpty do
      throwErrorAt stx "{operation}: the input is not a polynomial (it divides by a term with a \
        variable)"
    let some c := constValue? rational.value.den | throwErrorAt stx "{operation}: internal error"
    let p : MvPoly 1 := h ▸ scalePoly (1 / c) rational.value.num
    return (reified, toDense p)
  else
    throwErrorAt stx "{operation}: expected polynomials in one variable, found \
      {renderNames reified.names}"

/-- The common variable of several inputs, `x` when they have none. -/
def commonVariable (operation : String) (inputs : Array Syntax) : CommandElabM Name := do
  let mut names : List Name := []
  for stx in inputs do
    let reified ← parseInferred stx
    for name in reified.names do
      unless names.contains name do names := names ++ [name]
  match names with
  | [] => return `x
  | [x] => return x
  | _ => throwError "{operation}: expected polynomials in one variable, found \
      {renderNames names}"

/-- The input polynomial as a term of `ℚ[X]`. -/
def ringTermOf (reified : ReifiedExpr) : TermElabM (TSyntax `term) := do
  if h : 0 < reified.names.length then
    polynomialRingTerm (variableTerms reified) false ⟨0, h⟩ reified.expr
  else throwError "internal error: no variable"

/-- What a two-polynomial command computes. -/
inductive PairOperation where
  | gcd
  | lcm
  | quotientRemainder
  | quotient
  | remainder

/-- The `#cas` mode name of a two-polynomial operation, such as `polynomialGCD`. -/
def PairOperation.name : PairOperation → String
  | .gcd => "polynomialGCD"
  | .lcm => "polynomialLCM"
  | .quotientRemainder => "polynomialQuotientRemainder"
  | .quotient => "polynomialQuotient"
  | .remainder => "polynomialRemainder"

/-- Run a two-polynomial command on `(p, q)`. -/
def logPair (ref : Syntax) (operation : PairOperation) (left right : Syntax) :
    CommandElabM Unit := do
  let name := operation.name
  let x ← commonVariable name #[left, right]
  let (leftReified, p) ← denseOf name left x
  let (rightReified, q) ← denseOf name right x
  match operation with
  | .gcd =>
      if Dense.isZero p && Dense.isZero q then
        throwErrorAt ref "{name}: gcd 0 0 = 0 is not monic; give a nonzero polynomial"
  | .lcm =>
      if Dense.isZero p || Dense.isZero q then
        throwErrorAt ref "{name}: the polynomials must be nonzero (lcm 0 p = 0)"
  | _ =>
      if Dense.isZero q then throwErrorAt ref "{name}: division by the zero polynomial"
  let xText := renderName x
  let (proposition, proof, shown) : Lean.Expr × Lean.Expr × String ← liftTermElabM do
    let P ← ringTermOf leftReified
    let Q ← ringTermOf rightReified
    match operation with
    | .gcd =>
        let (g, G, script) ← gcdProof P Q p q
        let (a, b) ← proveStatement name (← `(gcd ($P) ($Q) = $G)) script
        pure (a, b, denseText xText g)
    | .lcm =>
        let (l, L, script) ← lcmProof P Q p q
        let (a, b) ← proveStatement name (← `(lcm ($P) ($Q) = $L)) script
        pure (a, b, denseText xText l)
    | .quotientRemainder | .quotient | .remainder =>
        let (s, r, S, R, script) ← divisionProof P Q p q
        let (a, b) ← proveStatement name (← `(($P) / ($Q) = $S ∧ ($P) % ($Q) = $R)) script
        let shown := match operation with
          | .quotient => denseText xText s
          | .remainder => denseText xText r
          | _ => s!"[{denseText xText s}, {denseText xText r}]"
        pure (a, b, shown)
  let evidence ← liftTermElabM <|
    checkedEvidence name "Statement in ℚ[X]" proposition proof
  logReport ref {
    domain := s!"{xText} ↦ X in ℚ[X]"
    input := s!"({leftReified.render}, {rightReified.render})"
    inputType := "polynomials"
    output := shown
    outputType := match operation with
      | .gcd => "monic gcd" | .lcm => "monic lcm"
      | .quotientRemainder => "[quotient, remainder]" | .quotient => "quotient"
      | .remainder => "remainder"
  } #[evidence]

/-- The polynomial of degree below `n` through `n` points with distinct abscissae (Lagrange). -/
def interpolate (points : List (ℚ × ℚ)) : Dense := Id.run do
  let mut total : Dense := #[]
  for (a, b) in points do
    let mut basis : Dense := #[1]
    for (c, _) in points do
      if c == a then continue
      basis := Dense.scale (1 / (a - c)) (Dense.mul basis #[-c, 1])
    total := Dense.add total (Dense.scale b basis)
  return total

/-- Run `#cas [interpolatingPolynomial x] points`. -/
def logInterpolating (ref : Syntax) (x : Name) (points : List (ℚ × ℚ)) : CommandElabM Unit := do
  let abscissae := points.map (·.1)
  unless abscissae.eraseDups.length == abscissae.length do
    throwErrorAt ref "interpolatingPolynomial: the abscissae must be distinct"
  if points.isEmpty then throwErrorAt ref "interpolatingPolynomial: no points"
  let p := interpolate points
  let xText := renderName x
  let (proposition, proof) ← liftTermElabM do
    let P ← qPolyTerm p
    let mut conditions : Array (TSyntax `term) := #[]
    for (a, b) in points do
      conditions := conditions.push
        (← `(Polynomial.eval (($(← ratSyntax a)) : ℚ) $P = $(← ratSyntax b)))
    conditions := conditions.push
      (← `(Polynomial.natDegree $P ≤ $(natTerm (points.length - 1))))
    let mut statement := conditions.back!
    for c in conditions.pop.reverse do
      statement ← `($c ∧ $statement)
    let evaluation ← `(tactic| first | (simp; done) | (simp; norm_num) | norm_num)
    let mut proofs : Array (TSyntax `term) := #[]
    for _ in points do
      proofs := proofs.push (← `(term| by $evaluation:tactic))
    proofs := proofs.push (← `(term| by (compute_degree <;> norm_num)))
    proveStatement "interpolatingPolynomial" statement (← `(tactic| exact ⟨$proofs,*⟩))
  let evidence ← liftTermElabM <|
    checkedEvidence "interpolatingPolynomial" "Values and degree in ℚ[X]" proposition proof
  logReport ref {
    domain := s!"{xText} ↦ X in ℚ[X]"
    input := ", ".intercalate (points.map fun (a, b) ↦ s!"({ratText a}, {ratText b})")
    inputType := "points"
    output := denseText xText p
    outputType := s!"polynomial of degree at most {points.length - 1}"
  } #[evidence]

/-- Parse `[(a₀, b₀), …]` or `[b₁, b₂, …]` (abscissae `1, 2, …`). -/
def parsePoints (stx : Syntax) : CommandElabM (List (ℚ × ℚ)) := do
  let literal (value : Syntax) : CommandElabM ℚ := parseRationalLiteralFor
    "interpolatingPolynomial" "the points must be exact rational literals, such as 2, -1/3 or 0.5"
    value
  match stx with
  | `([$entries,*]) =>
      let entries := entries.getElems.toList
      let mut out : List (ℚ × ℚ) := []
      for (entry, k) in entries.zipIdx do
        match entry with
        | `(($a, $b)) => out := out ++ [(← literal a, ← literal b)]
        | _ => out := out ++ [(((k + 1 : Nat) : ℚ), ← literal entry)]
      return out
  | _ => throwErrorAt stx "expected a list of points `[(a, b), …]` or of values `[b₁, b₂, …]`"

end CAS.Command.Algebra

namespace CAS.Command

open Lean Elab Command

/-- `#cas [polynomialGCD] (p, q)` prints the monic greatest common divisor of the polynomials `p`
and `q` in `ℚ[X]`.

## Theorem
With `x` read as `Polynomial.X`, the report proves `gcd p q = g` in `ℚ[X]`, for the normalized
gcd of Mathlib's `NormalizedGCDMonoid`. The proof divides `p` and `q` by `g` with explicit
cofactors, checks the Bézout identity `s * p + t * q = g` and the monicity of `g`.

## Conditions and limits
`p` and `q` are polynomials with rational coefficients in one variable, not both zero. The gcd is
monic.

## Options
None.

## Examples
```lean
#cas [polynomialGCD] (x^2 - 1, x^2 - 2*x + 1)
```
```output
Output (monic gcd): x - 1
```
```lean
#cas [polynomialGCD] (x^3 - 1, x^2 + 1)
```
```output
Output (monic gcd): 1
```
```lean
#cas [polynomialGCD] (2*x^2 + 3*x + 1, 4*x^2 - 1)
```
```output
Output (monic gcd): x + 1/2
```

## In a proof
```lean
open _root_.Polynomial in
theorem polynomialGCD_square : gcd (X ^ 2 - 1 : ℚ[X]) (X ^ 2 - 2 * X + 1) = X - 1 := by
  cas
```

## See also
Mathematica `PolynomialGCD`, SymPy `gcd`. The modes `polynomialLCM`, `polynomialQuotient`,
`polynomialRemainder` and `factor`.

## Possible issues
```lean
#cas [polynomialGCD] (x^2 - 1, y - 1)
```
```output
polynomialGCD: expected polynomials in one variable, found x, y
```
The mode works in one variable.
```lean
#cas [polynomialGCD] (0, 0)
```
```output
polynomialGCD: gcd 0 0 = 0 is not monic; give a nonzero polynomial
```
Give at least one nonzero polynomial.
-/
syntax (name := casPolynomialGCDCommand) "#cas" "[" &"polynomialGCD" "]" term : command

/-- `#cas [polynomialLCM] (p, q)` prints the monic least common multiple of the polynomials `p` and
`q` in `ℚ[X]`.

## Theorem
With `x` read as `Polynomial.X`, the report proves `lcm p q = l` in `ℚ[X]`, from `p ∣ l`, `q ∣ l`,
the gcd and `gcd_mul_lcm`.

## Conditions and limits
`p` and `q` are nonzero polynomials with rational coefficients in one variable. The lcm is monic.

## Options
None.

## Examples
```lean
#cas [polynomialLCM] (x^2 - 1, x^2 - 2*x + 1)
```
```output
Output (monic lcm): x^3 - x^2 - x + 1
```
```lean
#cas [polynomialLCM] (x^2 - 1, x^3 - 1)
```
```output
Output (monic lcm): x^4 + x^3 - x - 1
```

## In a proof
```lean
open _root_.Polynomial in
theorem polynomialLCM_square :
    lcm (X ^ 2 - 1 : ℚ[X]) (X ^ 2 - 2 * X + 1) = X ^ 3 - X ^ 2 - X + 1 := by
  cas
```

## See also
Mathematica `PolynomialLCM`, SymPy `lcm`. The modes `polynomialGCD` and `together`.

## Possible issues
```lean
#cas [polynomialLCM] (0, x)
```
```output
polynomialLCM: the polynomials must be nonzero (lcm 0 p = 0)
```
Give two nonzero polynomials.
-/
syntax (name := casPolynomialLCMCommand) "#cas" "[" &"polynomialLCM" "]" term : command

/-- `#cas [polynomialQuotientRemainder] (p, q)` prints the quotient and the remainder of the
Euclidean division of the polynomial `p` by `q` in `ℚ[X]`.

## Theorem
With `x` read as `Polynomial.X`, the report proves `p / q = s ∧ p % q = r` in `ℚ[X]`, from
`Polynomial.div_modByMonic_unique` for the monic divisor `q / lc q`, `Polynomial.div_def` and
`Polynomial.mod_def`.

## Conditions and limits
`p` and `q` are polynomials with rational coefficients in one variable, and `q` is nonzero. The
remainder has degree less than that of `q`.

## Options
None.

## Examples
```lean
#cas [polynomialQuotientRemainder] (x^3 + 1, 2*x - 1)
```
```output
Output ([quotient, remainder]): [1/2*x^2 + 1/4*x + 1/8, 9/8]
```
```lean
#cas [polynomialQuotientRemainder] (0, x + 1)
```
```output
Output ([quotient, remainder]): [0, 0]
```

## In a proof
```lean
open _root_.Polynomial in
theorem polynomialQuotientRemainder_linear :
    (X ^ 3 + 1 : ℚ[X]) / (2 * X - 1) = C (1 / 2) * X ^ 2 + C (1 / 4) * X + C (1 / 8) ∧
      (X ^ 3 + 1 : ℚ[X]) % (2 * X - 1) = C (9 / 8) :=
  ⟨by cas, by cas⟩
```

## See also
Mathematica `PolynomialQuotientRemainder`, SymPy `div`. The modes `polynomialQuotient`,
`polynomialRemainder` and `polynomialGCD`.

## Possible issues
```lean
#cas [polynomialQuotientRemainder] (x^2, 0)
```
```output
polynomialQuotientRemainder: division by the zero polynomial
```
Give a nonzero divisor. The tactic `cas` proves each part of the conjunction but not the
conjunction itself; prove it as `⟨by cas, by cas⟩`.
-/
syntax (name := casPolynomialQuotientRemainderCommand)
  "#cas" "[" &"polynomialQuotientRemainder" "]" term : command

/-- `#cas [polynomialQuotient] (p, q)` prints the quotient of the Euclidean division of the
polynomial `p` by `q` in `ℚ[X]`.

## Theorem
The report proves the statement of `#cas [polynomialQuotientRemainder] (p, q)`,
`p / q = s ∧ p % q = r` in `ℚ[X]`, and prints `s`.

## Conditions and limits
As for `#cas [polynomialQuotientRemainder]`.

## Options
None.

## Examples
```lean
#cas [polynomialQuotient] (x^4 - 1, x^2 + 1)
```
```output
Output (quotient): x^2 - 1
```
```lean
#cas [polynomialQuotient] (x^3 + 1, 2*x - 1)
```
```output
Output (quotient): 1/2*x^2 + 1/4*x + 1/8
```

## In a proof
```lean
open _root_.Polynomial in
theorem polynomialQuotient_square : (X ^ 4 - 1 : ℚ[X]) / (X ^ 2 + 1) = X ^ 2 - 1 := by
  cas
```

## See also
Mathematica `PolynomialQuotient`, SymPy `quo`. The modes `polynomialRemainder`,
`polynomialQuotientRemainder` and `polynomialGCD`.

## Possible issues
```lean
#cas [polynomialQuotient] (x^2, 0)
```
```output
polynomialQuotient: division by the zero polynomial
```
Give a nonzero divisor; Mathlib sets `p / 0 = 0`.
-/
syntax (name := casPolynomialQuotientCommand) "#cas" "[" &"polynomialQuotient" "]" term : command

/-- `#cas [polynomialRemainder] (p, q)` prints the remainder of the Euclidean division of the
polynomial `p` by `q` in `ℚ[X]`.

## Theorem
The report proves the statement of `#cas [polynomialQuotientRemainder] (p, q)`,
`p / q = s ∧ p % q = r` in `ℚ[X]`, and prints `r`.

## Conditions and limits
As for `#cas [polynomialQuotientRemainder]`.

## Options
None.

## Examples
```lean
#cas [polynomialRemainder] (x^5 + x + 1, x^2 + x + 1)
```
```output
Output (remainder): 0
```
```lean
#cas [polynomialRemainder] (x^3 + 1, 2*x - 1)
```
```output
Output (remainder): 9/8
```

## In a proof
```lean
open _root_.Polynomial in
theorem polynomialRemainder_linear : (X ^ 3 + 1 : ℚ[X]) % (2 * X - 1) = C (9 / 8) := by
  cas
```

## See also
Mathematica `PolynomialRemainder`, SymPy `rem`. The modes `polynomialQuotient`,
`polynomialQuotientRemainder` and `polynomialGCD`.

## Possible issues
```lean
#cas [polynomialRemainder] (x^2, 0)
```
```output
polynomialRemainder: division by the zero polynomial
```
Give a nonzero divisor; Mathlib sets `p % 0 = p`.
-/
syntax (name := casPolynomialRemainderCommand) "#cas" "[" &"polynomialRemainder" "]" term :
  command

/-- `#cas [interpolatingPolynomial x] [(a₀, b₀), …, (aₙ₋₁, bₙ₋₁)]` prints the polynomial of degree
at most `n - 1` in `x` that takes the value `bᵢ` at `aᵢ`.

## Theorem
For the printed polynomial `P` in `ℚ[X]`, the report proves the conjunction of `P.eval aᵢ = bᵢ`
for every point and `P.natDegree ≤ n - 1`, which makes `P` unique.

## Conditions and limits
The points are pairs of rational numbers with distinct abscissae. A list of values
`[b₁, b₂, …]` stands for the points `(1, b₁), (2, b₂), …`.

## Options
None.

## Examples
```lean
#cas [interpolatingPolynomial x] [(0, 1), (1, 3), (2, 7)]
```
```output
Output (polynomial of degree at most 2): x^2 + x + 1
```
```lean
#cas [interpolatingPolynomial x] [1, 4, 9, 16]
```
```output
Output (polynomial of degree at most 3): x^2
```
```lean
#cas [interpolatingPolynomial x] [(1/2, 1), (2, 0), (3, 5)]
```
```output
Output (polynomial of degree at most 2): 34/15*x^2 - 19/3*x + 18/5
```

## In a proof
```lean
open _root_.Polynomial in
theorem interpolatingPolynomial_eval : (X ^ 2 + X + 1 : ℚ[X]).eval 2 = 7 := by
  cas
```

## See also
Mathematica `InterpolatingPolynomial`, SymPy `interpolate`. The modes `polynomialGCD`, `solve`
and `coefficientList`.

## Possible issues
```lean
#cas [interpolatingPolynomial x] [(0, 1), (0, 2)]
```
```output
interpolatingPolynomial: the abscissae must be distinct
```
Two values at the same point have no interpolating polynomial; remove one of them.
```lean
#cas [interpolatingPolynomial x] (1, 2)
```
```output
expected a list of points `[(a, b), …]` or of values `[b₁, b₂, …]`
```
Write the points in square brackets.
-/
syntax (name := casInterpolatingPolynomialCommand)
  "#cas" "[" &"interpolatingPolynomial" ident "]" term : command

/-- The two polynomials of a pair `(p, q)`. -/
def Algebra.pairOf (stx : Syntax) : CommandElabM (Syntax × Syntax) := do
  match stx with
  | `(($p, $q)) => return (p, q)
  | _ => throwErrorAt stx "expected a pair of polynomials `(p, q)`"

elab_rules : command
  | `(#cas [polynomialGCD] $e:term) => do
      let (p, q) ← Algebra.pairOf e
      Algebra.logPair e .gcd p q
  | `(#cas [polynomialLCM] $e:term) => do
      let (p, q) ← Algebra.pairOf e
      Algebra.logPair e .lcm p q
  | `(#cas [polynomialQuotientRemainder] $e:term) => do
      let (p, q) ← Algebra.pairOf e
      Algebra.logPair e .quotientRemainder p q
  | `(#cas [polynomialQuotient] $e:term) => do
      let (p, q) ← Algebra.pairOf e
      Algebra.logPair e .quotient p q
  | `(#cas [polynomialRemainder] $e:term) => do
      let (p, q) ← Algebra.pairOf e
      Algebra.logPair e .remainder p q
  | `(#cas [interpolatingPolynomial $x:ident] $e:term) => do
      Algebra.logInterpolating e x.getId (← Algebra.parsePoints e)

end CAS.Command
