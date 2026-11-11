/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.DSolveOrder
public import CAS.Command.RootSplit
public meta import CAS.Polynomial.RealRoot.RadicalGenerator
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses

/-!
# All complex roots of a polynomial: `#cas [roots z in ℂ]`

`#cas [roots z in ℂ] (p = q)` lists every complex solution of a polynomial equation with rational
coefficients in one variable, each root once. The roots are named by certified enclosures:
`AlgRoot.real S lo hi` for a real root in `(lo, hi)` and `AlgRoot.complex S u v ρ` for a complex
root within `ρ` of `u + v i`, with `S` the monic radical of `p - q`, one root of each conjugate
pair. The theorem is

`let r₁ := …; let z₁ := …; (enclosures) ∧ ∀ z : ℂ, p z - q z = 0 ↔ z ∈ [↑r₁, …, z₁, conj z₁, …]`,

with `p - q` expanded. When every root is a Gaussian rational the report lists the roots exactly
and the theorem is `∀ z : ℂ, p z - q z = 0 ↔ z = w₁ ∨ ⋯ ∨ z = wₖ`, for `z ^ 2 + 1 = 0` the
equivalence `z = Complex.I ∨ z = -Complex.I`.

## Implementation notes

The radical comes from `CAS.Polynomial.RealRoot.RadicalCertificate.generate?`
(`CAS/Polynomial/RealRoot/RadicalGenerator.lean`) with the identities `S G = R` and `R H = Sᵐ`
for the monic `R`, which the kernel checks and which give the same roots
(`AlgRoot.eval_eq_zero_iff_of_radical`). The enclosures are those of `CAS.Command.RootSplit`
(`enclose`: floating-point Durand-Kerner roots refined by exact Newton steps, see
`CAS/Command/RootSplit.lean`); no simultaneous iteration runs here. The kernel decides
`LinearODE.Enclosures.check` and, for each enclosure, the sign change or the `AlgRoot.cCheck`
bounds that place the root (`AlgRoot.real_spec`, `AlgRoot.complex_spec`), and
`LinearODE.Enclosures.eval_eq_zero_iff` gives the list.

For the exact form, the candidates are the points nearest to the centres of the enclosures on a
grid whose spacing Gauss's lemma bounds (`gridScale`); they are kept when they divide `p - q` out
exactly, and `linear_combination` with `Complex.I ^ 2 = -1` proves the factorization
`(∏ (z - wᵢ) ^ mᵢ) c = p z - q z` that the equivalence follows from. The grid only proposes
candidates, so the lemma needs no proof here.
-/

public meta section

namespace CAS.Command.ComplexRoots

open Lean Elab Command Meta Term
open CAS.Command.InfoView
open CAS.Command.SpecialFunctions
open CAS.Command.ExpPolynomials
open CAS.Command.RootSplit
open CAS.Command.Algebra (Dense)
open CAS.Verified.Expr

/-! ## Gaussian rational roots -/

/-- `2 L` for the leading coefficient `L` of the primitive integer multiple of the monic `S`. The
real and imaginary parts of a Gaussian rational root of `S` are multiples of `1 / (2 L)`: by
Gauss's lemma its minimal polynomial over `ℤ`, `c z - c a` or
`c z ^ 2 - 2 a c z + c (a ^ 2 + b ^ 2)`, divides that multiple, so `c ∣ L`, and `2 a c` and
`2 b c` are integers. -/
private def gridScale (S : Dense) : ℕ :=
  let scale := S.foldl (fun l c ↦ Nat.lcm l c.den) 1
  let content := S.foldl (fun g c ↦ Nat.gcd g (c * (scale : ℚ)).num.natAbs) 0
  2 * (scale / max content 1)

/-- The quotient and the remainder of `p` by `z - w`, by Horner's scheme. -/
private def divLinear (p : CPoly) (w : GaussianRat) : CPoly × GaussianRat := Id.run do
  if p.size ≤ 1 then return (#[], p.getD 0 default)
  let mut quotient : CPoly := Array.replicate (p.size - 1) default
  let mut carry := p.getD (p.size - 1) default
  for i in [0:p.size - 1] do
    let k := p.size - 2 - i
    quotient := quotient.set! k carry
    carry := p.getD k default + w * carry
  return (quotient, carry)

/-- The roots of the monic `R` with their multiplicities, when they are all Gaussian rationals:
the points of the grid of `gridScale S` nearest to the centres of the enclosures `D` of the roots
of the radical `S`, refined by Newton steps, kept when dividing them out of `R` leaves `1`. -/
private def gaussianRoots? (S R : Dense) (D : LinearODE.Enclosures) :
    Option (List (GaussianRat × ℕ)) := Id.run do
  let scale : ℚ := gridScale S
  let nearest (x : ℚ) : ℚ := ((x * scale + 1 / 2).floor : ℚ) / scale
  let reals : List GaussianRat := D.reals.map fun (lo, hi) ↦
    GaussianRat.ofRat (nearest (refineReal S.toList ((lo + hi) / 2)))
  let pairs : List GaussianRat := D.discs.flatMap fun (u, v, _) ↦
    let (re, im) := refineComplex S.toList u v
    [GaussianRat.mk (nearest re) (nearest im), GaussianRat.mk (nearest re) (-nearest im)]
  let mut rest : CPoly := R.map GaussianRat.ofRat
  let mut roots : List (GaussianRat × ℕ) := []
  for w in reals ++ pairs do
    let mut count := 0
    for _ in [0:R.size] do
      let (quotient, remainder) := divLinear rest w
      unless remainder.isZero && !quotient.isEmpty do break
      rest := quotient
      count := count + 1
    if count = 0 then return none
    roots := roots ++ [(w, count)]
  return if rest == #[GaussianRat.ofRat 1] then some roots else none

/-- Polynomials in `z` and `i` with rational coefficients: the entry `j` holds the coefficients
of `i ^ j z ^ k`, by `k`. -/
private abbrev BiPoly := Array (Array ℚ)

/-- `p q`. -/
private def biMul (p q : BiPoly) : BiPoly := Id.run do
  let width (a : BiPoly) : ℕ := a.foldl (fun m row ↦ max m row.size) 0
  let mut out : BiPoly :=
    Array.replicate (p.size + q.size - 1) (Array.replicate (width p + width q) 0)
  for j₁ in [0:p.size] do
    let row₁ := p.getD j₁ #[]
    for k₁ in [0:row₁.size] do
      let a := row₁.getD k₁ 0
      if a == 0 then continue
      for j₂ in [0:q.size] do
        let row₂ := q.getD j₂ #[]
        for k₂ in [0:row₂.size] do
          let b := row₂.getD k₂ 0
          out := out.modify (j₁ + j₂) fun row ↦ row.modify (k₁ + k₂) (· + a * b)
  return out

/-- `(∏ (z - wᵢ) ^ mᵢ) lead - p` as a polynomial in `z` and `i`. -/
private def factorizationDefect (roots : List (GaussianRat × ℕ)) (lead : ℚ) (p : Dense) :
    BiPoly :=
  let product : BiPoly := roots.foldl (fun acc (w, m) ↦
    (List.range m).foldl (fun acc _ ↦ biMul acc #[#[-w.re, 1], #[-w.im]]) acc) #[#[1]]
  (product.map (·.map (· * lead))).modify 0 fun row ↦
    (Array.range (max row.size p.size)).map fun k ↦ row.getD k 0 - p.getD k 0

/-- The quotient `c` of `p = c (i ^ 2 + 1)`, when the division leaves no remainder. -/
private def divISq? (p : BiPoly) : Option BiPoly := Id.run do
  let mut rest := p
  let mut quotient : BiPoly := Array.replicate (p.size - 2) #[]
  for i in [0:p.size - 2] do
    let j := p.size - 1 - i
    let row := rest.getD j #[]
    quotient := quotient.set! (j - 2) row
    rest := rest.modify (j - 2) fun lower ↦
      (Array.range (max lower.size row.size)).map fun k ↦ lower.getD k 0 - row.getD k 0
    rest := rest.set! j #[]
  return if rest.all (·.all (· == 0)) then some quotient else none

/-- The polynomial `p` in `z` and `Complex.I` as syntax. -/
private def biSyntax (p : BiPoly) (z : TSyntax `term) : TermElabM (TSyntax `term) := do
  let mut terms : Array (TSyntax `term) := #[]
  for j in [0:p.size] do
    let row := p.getD j #[]
    for k in [0:row.size] do
      let c := row.getD k 0
      if c == 0 then continue
      let jLit := Syntax.mkNumLit (toString j)
      let kLit := Syntax.mkNumLit (toString k)
      terms := terms.push (← `(($(← ratSyntax c) : ℂ) * Complex.I ^ $jLit * $z ^ $kLit))
  match terms.toList with
  | [] => `((0 : ℂ))
  | first :: rest => rest.foldlM (fun sum term ↦ `($sum + $term)) first

/-- The Gaussian rational `w` as a complex term: `a`, `b * Complex.I`, `a + b * Complex.I` or
`a - b * Complex.I`, with `Complex.I` alone for `b = 1`. -/
private def gaussianTerm (w : GaussianRat) : TermElabM (TSyntax `term) := do
  let magnitude := if w.im < 0 then -w.im else w.im
  let imaginary ← if magnitude == 1 then `(Complex.I)
    else `($(← ratSyntax magnitude) * Complex.I)
  if w.im == 0 then `(($(← ratSyntax w.re) : ℂ))
  else if w.re == 0 then (if w.im < 0 then `(-$imaginary) else pure imaginary)
  else if w.im < 0 then `($(← ratSyntax w.re) - $imaginary)
  else `($(← ratSyntax w.re) + $imaginary)

/-- The Gaussian rational `w` as the calculator writes it: `a`, `b*i`, `a + b*i` or `a - b*i`,
with `i` alone for `b = 1`. -/
private def gaussianText (w : GaussianRat) : String :=
  let magnitude := if w.im < 0 then -w.im else w.im
  let imaginary := if magnitude == 1 then "i" else s!"{magnitude}*i"
  if w.im == 0 then toString w.re
  else if w.re == 0 then (if w.im < 0 then "-" else "") ++ imaginary
  else s!"{w.re} {if w.im < 0 then "-" else "+"} {imaginary}"

/-- Report the roots of `p = q` exactly, when they are the Gaussian rationals `roots`: the theorem
`∀ z : ℂ, p - q = 0 ↔ z = w₁ ∨ ⋯ ∨ z = wₖ`, from the factorization
`(∏ (z - wᵢ) ^ mᵢ) lead = p - q`, which `linear_combination` proves with the multiple of
`Complex.I ^ 2 = -1` that `divISq?` computes. `false` when that multiple does not exist. -/
private def logGaussianRoots (ref : Syntax) (z : TSyntax `ident) (input : Syntax) (coeffs : Dense)
    (roots : List (GaussianRat × ℕ)) : CommandElabM Bool := do
  let lead := Dense.lead coeffs
  let some multiple := divISq? (factorizationDefect roots lead coeffs) | return false
  let zT : TSyntax `term := ⟨z.raw⟩
  let factorization := mkIdent `hfactorization
  let proof ← liftTermElabM do
    let terms ← roots.toArray.mapM fun (w, _) ↦ gaussianTerm w
    let factors ← (roots.toArray.zip terms).mapM fun ((_, m), t) ↦
      `(($zT - $t) ^ $(Syntax.mkNumLit (toString m)))
    let some lastFactor := factors.back? | throwError "roots: no root"
    let product ← factors.pop.foldrM (fun factor acc ↦ `($factor * $acc)) lastFactor
    let some lastTerm := terms.back? | throwError "roots: no root"
    let disjunction ← terms.pop.foldrM (fun t acc ↦ `($zT = $t ∨ $acc)) (← `($zT = $lastTerm))
    let poly ← polySyntax coeffs.toList zT (← `(ℂ))
    let statement ← `(∀ $z:ident : ℂ, $poly = 0 ↔ $disjunction)
    -- `mul_eq_zero`, `pow_eq_zero_iff` and `sub_eq_zero` for each factor, the first factor first.
    let mut rules : Array (TSyntax ``Lean.Parser.Tactic.rwRule) := #[]
    for i in [0:factors.size] do
      if i + 1 < factors.size then
        rules := rules.push (← `(Lean.Parser.Tactic.rwRule| mul_eq_zero))
      rules := rules.push (← `(Lean.Parser.Tactic.rwRule| pow_eq_zero_iff (by norm_num)))
      rules := rules.push (← `(Lean.Parser.Tactic.rwRule| sub_eq_zero))
    let proofT ← `(fun $z:ident ↦ by
      have $factorization:ident : $product * ($(← ratSyntax lead) : ℂ) = $poly := by
        linear_combination ($(← biSyntax multiple zT)) * Complex.I_sq
      rw [← $factorization:ident, mul_eq_zero, or_iff_left (by norm_num)]
      rw [$rules,*])
    let proof ← elabCheckedProof "roots" statement proofT
    CAS.Tactic.Explanation.kernelCheckedProof "roots" (← inferType proof) proof
  let report ← liftTermElabM do
    evidenceReportMessage
      #[← CAS.Tactic.Explanation.UncheckedExplanationStep.ofProof
        "The complex roots and no other root" proof]
  logReport ref {
    domain := s!"{z.getId} ∈ ℂ"
    input := surfaceText input
    inputType := "polynomial equation with rational coefficients"
    output := ", ".intercalate (roots.map (gaussianText ·.1))
    outputType := if roots.length == 1 then "the only complex root"
      else s!"all {roots.length} distinct complex roots"
  } #[report]
  return true

/-- Run `#cas [roots z in ℂ] (p = q)`. -/
def logComplexRoots (ref : Syntax) (z : TSyntax `ident) (input : Syntax) : CommandElabM Unit := do
  let (lhs, rhs) ← match unparen input with
    | `($l:term = $r:term) => pure (l, r)
    | _ => throwErrorAt input "roots: expected an equation p = q"
  let reified ← parseExact (← `($lhs - $rhs)) [z.getId]
  unless reified.names.length = 1 do
    throwErrorAt input "roots: the equation may depend only on {z.getId}"
  let E : Verified.Expr (Fin 1) := reified.expr.mapVars fun _ ↦ (.var 0 : Verified.Expr (Fin 1))
  let some f := toExpPoly E | throwErrorAt input "roots: the equation is not polynomial"
  let mut a : Dense := #[]
  for (l, Pc) in f do
    unless l.re = 0 && l.im = 0 do throwErrorAt input "roots: the equation is not polynomial"
    for k in [0:Pc.size] do
      let c := Pc.getD k default
      unless c.im = 0 do throwErrorAt input "roots: unexpected complex coefficient"
      while a.size ≤ k do a := a.push 0
      a := a.set! k (a.getD k 0 + c.re)
  let coeffs := Dense.trim a
  unless coeffs.size ≥ 2 do
    throwErrorAt input "roots: the polynomial must have degree one or more"
  let lead := Dense.lead coeffs
  let R := Dense.scale (1 / lead) coeffs
  -- The radical `S` with `S G = R` and `R H = Sᵐ`: the checked radical certificate, made monic.
  let some ⟨certificate, _⟩ := CAS.Polynomial.RealRoot.RadicalCertificate.generate?
      (CAS.Polynomial.Sparse.ofCoeffs R.toList)
    | throwErrorAt input "roots: the radical of the polynomial could not be computed"
  let dense (p : CAS.Polynomial.Sparse.Univariate) : Dense :=
    Dense.trim (CAS.Polynomial.Sparse.coeffs p).toArray
  let leading := Dense.lead (dense certificate.radical)
  let m := certificate.exponent.val
  let S := Dense.scale (1 / leading) (dense certificate.radical)
  let G := Dense.scale leading (dense certificate.originalOverRadical)
  let H := Dense.scale (1 / leading ^ m) (dense certificate.radicalPowerOverOriginal)
  unless CAS.Polynomial.coeffMul S.toList G.toList == R.toList &&
      CAS.Polynomial.coeffMul R.toList H.toList == CAS.Polynomial.coeffPow S.toList m do
    throwErrorAt input "roots: the radical of the polynomial could not be computed"
  let D ← match enclose S with
    | .ok D => pure D
    | .error msg => throwErrorAt input "roots: {msg}"
  if let some roots := gaussianRoots? S R D then
    if (← logGaussianRoots ref z input coeffs roots) then return
  let zT : TSyntax `term := ⟨z.raw⟩
  let proof ← liftTermElabM do
    let certified (prop : TSyntax `term) : TermElabM (TSyntax `term) := do
      let type ← elabType prop
      synthesizeSyntheticMVarsNoPostponing
      let type ← instantiateMVars type
      exprToSyntax (← CAS.CEGA.Elaboration.decideClosedCertificate type false)
    let RT ← `(($(← listSyntax (← R.mapM ratQ)) : List ℚ))
    let ST ← `(($(← listSyntax (← S.mapM ratQ)) : List ℚ))
    let GT ← `(($(← listSyntax (← G.mapM ratQ)) : List ℚ))
    let HT ← `(($(← listSyntax (← H.mapM ratQ)) : List ℚ))
    let hg ← certified (← `(CAS.Polynomial.coeffMul $ST $GT = $RT))
    let mT : TSyntax `term := Syntax.mkNumLit (toString m)
    let hh ← certified (← `(CAS.Polynomial.coeffMul $RT $HT = CAS.Polynomial.coeffPow $ST $mT))
    let realsT ← listSyntax (← D.reals.toArray.mapM fun (lo, hi) ↦ do
      `(($(← boundQ lo), $(← boundQ hi))))
    let discsT ← listSyntax (← D.discs.toArray.mapM fun (u, v, ρ, κ, Rb, L) ↦ do
      `(($(← boundQ u), $(← boundQ v), $(← boundQ ρ), $(← ratQ κ), $(← ratQ Rb), $(← ratQ L))))
    let DT ← `((⟨$realsT, $discsT⟩ : LinearODE.Enclosures))
    let hD ← certified (← `(LinearODE.Enclosures.check $ST $DT = true))
    let mut enclosuresT : Array (TSyntax `term) := #[]
    let mut enclosureProofs : Array (TSyntax `term) := #[]
    let mut members : Array (TSyntax `term) := #[]
    let h₁ := mkIdent `h₁
    let h₂ := mkIdent `h₂
    for (lo, hi) in D.reals do
      let loT ← boundQ lo
      let hiT ← boundQ hi
      let r ← `(AlgRoot.real $ST $loT $hiT)
      members := members.push (← `((($r : ℝ) : ℂ)))
      let hlt ← certified (← `(($loT : ℚ) < $hiT))
      let hsign ← certified (← `((CAS.Polynomial.coeffEvalRat $ST $loT) *
        (CAS.Polynomial.coeffEvalRat $ST $hiT) < 0))
      enclosuresT := enclosuresT.push (← `($r ∈ Set.Ioo $(← boundR lo) $(← boundR hi)))
      enclosureProofs := enclosureProofs.push (← `(by
        have $h₁:ident := (AlgRoot.real_spec $ST $hlt $hsign).1
        push_cast at $h₁:ident
        exact ⟨by linarith [($h₁).1], by linarith [($h₁).2]⟩))
    for (u, v, ρ, κ, Rb, L) in D.discs do
      let uT ← boundQ u
      let vT ← boundQ v
      let ρT ← boundQ ρ
      let w ← `(AlgRoot.complex $ST $uT $vT $ρT)
      members := members.push w
      members := members.push (← `((starRingEnd ℂ) $w))
      let hcc ← certified (← `(AlgRoot.cCheck $ST $uT $vT $ρT $(← ratQ κ) $(← ratQ Rb)
        $(← ratQ L) = true))
      enclosuresT := enclosuresT.push (← `(($w).re ∈
          Set.Icc $(← boundR (u - ρ)) $(← boundR (u + ρ)) ∧
        ($w).im ∈ Set.Icc $(← boundR (v - ρ)) $(← boundR (v + ρ))))
      enclosureProofs := enclosureProofs.push (← `(⟨by
          have $h₁:ident := (AlgRoot.re_mem_of_mem_closedBall (AlgRoot.complex_spec $ST $hcc).1).1
          push_cast at $h₁:ident
          exact ⟨by linarith [($h₁).1], by linarith [($h₁).2]⟩, by
          have $h₂:ident := (AlgRoot.re_mem_of_mem_closedBall (AlgRoot.complex_spec $ST $hcc).1).2
          push_cast at $h₂:ident
          exact ⟨by linarith [($h₂).1], by linarith [($h₂).2]⟩⟩))
    let poly ← polySyntax coeffs.toList zT (← `(ℂ))
    let leadT ← `((($(← ratQ lead) : ℚ) : ℂ))
    let listT ← `(([$members,*] : List ℂ))
    let complete ← `(∀ $z:ident : ℂ, $poly = 0 ↔ $zT ∈ $listT)
    let statement ← enclosuresT.foldrM (fun e acc ↦ `($e ∧ $acc)) complete
    let completeProof ← `(fun $z:ident ↦ by
      have e : ((AlgRoot.polyC $RT).eval $zT) * $leadT = $poly := by
        simp only [AlgRoot.polyC_cons, AlgRoot.polyC_nil, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_zero]
        push_cast
        ring
      rw [← e, mul_eq_zero, or_iff_left (by norm_num),
        AlgRoot.eval_eq_zero_iff_of_radical $hg $hh,
        LinearODE.Enclosures.eval_eq_zero_iff $ST $DT $hD]
      rfl)
    let proofT ← `(⟨$enclosureProofs,*, $completeProof⟩)
    let proof ← elabCheckedProof "roots" statement proofT
    let cleaned ← Digits.cleanProof proof [``Rat.cast_neg, ``Rat.cast_div, ``Rat.cast_natCast,
      ``Rat.cast_intCast, ``Rat.cast_one, ``Rat.cast_zero, ``Rat.cast_ofNat] [] (simprocs := true)
    let cleaned ← evaluateNumerals cleaned
    let named := Digits.restoreNames (← inferType proof) (← inferType cleaned)
    let withLets ← letRoots named
    let cleaned ← mkExpectedTypeHint cleaned withLets
    CAS.Tactic.Explanation.kernelCheckedProof "roots" withLets cleaned
  let report ← liftTermElabM do
    evidenceReportMessage
      #[← CAS.Tactic.Explanation.UncheckedExplanationStep.ofProof
        "The complex roots, by certified enclosures, and no other root" proof]
  let realText := (D.reals.zipIdx.map fun ((lo, hi), i) ↦
    s!"r{Nat.toSubscriptString (i + 1)} ∈ ({decimal lo}, {decimal hi})")
  let discText := (D.discs.zipIdx.map fun ((u, v, ρ, _), i) ↦
    s!"z{Nat.toSubscriptString (i + 1)}, conj z{Nat.toSubscriptString (i + 1)} = α ± iβ, \
      α ∈ [{decimal (u - ρ)}, {decimal (u + ρ)}], β ∈ [{decimal (v - ρ)}, {decimal (v + ρ)}]")
  logReport ref {
    domain := s!"{z.getId} ∈ ℂ"
    input := surfaceText input
    inputType := "polynomial equation with rational coefficients"
    output := ", ".intercalate (realText ++ discText)
    outputType := if S.size == 2 then "the only complex root, by a certified enclosure"
      else s!"all {S.size - 1} distinct complex roots, by certified enclosures"
  } #[report]

end CAS.Command.ComplexRoots

namespace CAS.Command

open Lean Elab Command

/-- `#cas [roots z in ℂ] (lhs = rhs)` lists every complex solution of a polynomial equation with
rational coefficients once and proves that the list is complete, for the expanded difference `p`
of the two sides. When every root is a Gaussian rational, the roots are exact, as `i` and `-i`
for `z ^ 2 + 1 = 0`, and the theorem is `∀ z : ℂ, p = 0 ↔ z = w₁ ∨ … ∨ z = wₖ`. Otherwise the
real roots are certified enclosures `rᵢ ∈ (l, u)`, the others are pairs `zᵢ, conj zᵢ = α ± iβ`
with intervals for `α` and `β`, and the theorem is `∀ z : ℂ, p = 0 ↔ z ∈ [r₁, …, z₁, conj z₁, …]`.
See `#cas [roots x]` for the real roots.
-/
syntax (name := casComplexRootsCommand) "#cas" "[" &"roots" ident " in " "ℂ" "]" term : command

elab_rules : command
  | `(#cas [roots $z:ident in ℂ] $eq:term) => ComplexRoots.logComplexRoots eq z eq

end CAS.Command
