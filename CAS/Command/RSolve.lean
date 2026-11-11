/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.LinearAlgebra.Basic
public import CAS.Command.Sum
public import CAS.Command.RootSplit
public import CAS.Command.ExpPolynomials
public import CAS.Calculus.LinearRecurrence
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public meta import CAS.Calculus.LinearRecurrence
public meta import CAS.Calculus.LinearODERoots

/-!
# Linear recurrences: `#cas [rsolve a n]`

`#cas [rsolve a n] (a (n + 2) = a (n + 1) + a n)` solves a linear recurrence with constant
rational coefficients, and `#cas [rsolve a n, a 0 = 0, a 1 = 1] (…)` gives the single solution
with the given initial values, which may sit at any `d` consecutive indices for a recurrence of
order `d`. The right side may contain terms `c nʲ rⁿ` in `n`. A characteristic root `r` of
multiplicity `k` contributes `nʲ rⁿ` for `j < k`, a pair of complex roots `z, z̄` contributes
`nʲ Re zⁿ` and `nʲ Im zⁿ`, and the roots without closed form are named by enclosures
`AlgRoot.real R lo hi` and `AlgRoot.complex R u v ρ`. The enclosures come first in the statement,
with the equation of each root, and the roots are named `r₁, z₁, …` by `let`.

Without initial values the theorem is
`∀ a : ℕ → ℝ, (∀ n, recurrence) ↔ ∃ c₁ … c_d, ∀ n, a n = yp n + c₁ φ₁ n + ⋯ + c_d φ_d n`, by
`LinearRecurrence.rec_general`. With them it is
`∀ a : ℕ → ℝ, ((∀ n, recurrence) ∧ initial values) ↔ ∀ n, a n = Y n`, by
`LinearRecurrence.rec_ivp`.

## Implementation notes

The search is untrusted. `particular` finds `yp` by undetermined coefficients: for a term
`rⁿ P (n)` of the right side, with `k` the multiplicity of `r` as a root of the characteristic
polynomial (`0` when it is not a root), it takes `∑ eₜ n ^ (k + t) rⁿ` with one unknown `eₜ` for
each coefficient of `P` and solves the square rational system of the equations at the first
indices. `CAS.Command.RootSplit` splits the characteristic polynomial: rational roots, the roots
`α ± c √m` and `α ± i c √m` of quadratic factors, the factors of the registered factor provider,
and enclosures of the roots of the remaining factor `R`. With initial values `ivpWeights` solves
a square rational system for the coefficients of `Y`. A pair of real roots `α ± c √m` enters as
`r₊ⁿ + r₋ⁿ` and `(r₊ⁿ - r₋ⁿ) / √m`, a pair `z, z̄` as `Re zⁿ` and `Im zⁿ / √m`, whose values
`quadPow` gives as rational numbers (so Binet's formula comes out with rational coefficients). The
enclosed roots enter through `LinearRecurrence.encSeq`, the sum `∑ G(μ) μⁿ` over the roots `μ` of
`R` for a rational polynomial `G`, whose value at `N` is a coefficient of the remainder of
`G R' X ^ N` by `R` (`encDivision`), a rational number too.

The kernel decides the separation and the enclosures of the roots and, at the initial indices,
the values of `quadUV` and the divisions of `LinearRecurrence.encSeq_eq`; tactic proofs restate
the recurrence in normal form (`linear_combination`), check that `yp` solves it (`push_cast`,
`ring`) and add the values (`norm_num`). The theorems are in
`CAS/Calculus/LinearRecurrence.lean`.

## References

* Mitchel T. Keller and William T. Trotter, *Applied Combinatorics*, 2017.3 ed.,
  <https://www.rellek.net/book/app-comb.html>. `particular` takes the guess of Section 9.4.2
  (Examples 9.14 to 9.17): the shape of the right side, with the powers of `n` raised past the
  solutions of the homogeneous equation and all lower powers kept. The book matches coefficients;
  we solve for the unknowns from the values at the first indices.
-/

public meta section

namespace CAS.Command.RSolve

open Lean Elab Command Meta Term
open CAS.Command.InfoView
open CAS.Command.Algebra (ratText checkedEvidence Dense)
open CAS.Command.LinearAlgebra (QMatrix)
open CAS.Command.RootSplit
open CAS.LinearODE (CharRoot Enclosures)

/-! ## Parsing -/

/-- A linear combination `∑ cⱼ a (n + j) + g (n)`. -/
structure LinearPart where
  /-- The coefficients of the shifts. -/
  coefficients : List (Nat × ℚ) := []
  /-- The terms in `n` alone, as an expression in `n`. -/
  rest : Option (Verified.Expr (Fin 1)) := none

namespace LinearPart

/-- `c x`. -/
def scale (c : ℚ) (x : LinearPart) : LinearPart :=
  { coefficients := x.coefficients.map fun (j, a) ↦ (j, c * a)
    rest := x.rest.map fun r ↦ .mul (CAS.Command.ratExpr c) r }

/-- `x + y`. -/
def add (x y : LinearPart) : LinearPart :=
  { coefficients := y.coefficients.foldl (fun acc (j, a) ↦
      match acc.find? (·.1 == j) with
      | some _ => acc.map fun (i, b) ↦ if i == j then (i, a + b) else (i, b)
      | none => acc ++ [(j, a)]) x.coefficients
    rest := match x.rest, y.rest with
      | some r, some s => some (.add r s)
      | some r, none => some r
      | none, s => s }

end LinearPart

/-- A term free of the sequence, read as an expression in the index. -/
def inTermsOfIndex (index : Name) (stx : Syntax) : CommandElabM LinearPart := do
  let reified ← parseExact stx [index]
  match reified with
  | ⟨[_], expression, _⟩ => return { rest := some expression }
  | _ => throwErrorAt stx "rsolve: expected a term in {index}"

/-- The value of a constant part. -/
def constantPart? (x : LinearPart) : Option ℚ :=
  if !x.coefficients.isEmpty then none else
  match x.rest with
  | none => some 0
  | some r =>
      match Algebra.rationalOfExpr r with
      | .ok rational =>
          if rational.value.isPoly then
            let num := Algebra.constValue? rational.value.num
            match num, Algebra.constValue? rational.value.den with
            | some c, some d => some (c / d)
            | _, _ => none
          else none
      | .error _ => none

/-- The shift `k` of an argument `n` or `n + k`. -/
def shiftOf (index : Name) (arg : Syntax) : CommandElabM Nat := do
  match LinearAlgebra.unparen arg with
  | `($i:ident) =>
      if i.getId == index then return 0
      else throwErrorAt arg "rsolve: expected {index} or {index} + k"
  | `($i:ident + $k:num) =>
      if i.getId == index then return k.getNat
      else throwErrorAt arg "rsolve: expected {index} or {index} + k"
  | _ => throwErrorAt arg "rsolve: expected {index} or {index} + k"

/-- Whether `arg` is the index `n` or a shift `n + k`, the argument of a term of a sequence. -/
def isShift (index : Name) (arg : Syntax) : Bool :=
  match LinearAlgebra.unparen arg with
  | `($i:ident) => i.getId == index
  | `($i:ident + $_:num) => i.getId == index
  | _ => false

/-- Whether the syntax mentions the identifier `index`. -/
partial def mentions (index : Name) : Syntax → Bool
  | .ident _ _ n _ => n == index
  | .node _ _ args => args.any (mentions index)
  | _ => false

/-- Parse one side of the recurrence. -/
partial def parseSide (seq index : Name) (stx : Syntax) : CommandElabM LinearPart := do
  let linear (stx : Syntax) : CommandElabM LinearPart :=
    throwErrorAt stx "rsolve: the recurrence must be linear in {seq}"
  let coefficient (factor term : Syntax) (text : String) : CommandElabM LinearPart :=
    if mentions index factor then
      throwErrorAt stx "rsolve: recurrences with coefficients that depend on {index} are not \
        treated (the coefficient of {surfaceText term} is {text})"
    else
      throwErrorAt stx "rsolve: the coefficient {text} of {surfaceText term} is not a rational \
        number"
  match stx with
  | `(($e)) => parseSide seq index e
  | `($f:ident $arg:term) =>
      if f.getId == seq then
        return { coefficients := [(← shiftOf index arg, 1)] }
      else
        -- A function unknown to the expression parser, applied to `n` or `n + k`, is a term of
        -- another sequence than the one the mode names.
        try inTermsOfIndex index stx
        catch e =>
          if isShift index arg then
            throwErrorAt f "rsolve: the equation is about the sequence {f.getId}, but the mode \
              names {seq}; write #cas [rsolve {f.getId} {index}]"
          else throw e
  | `($x + $y) => return (← parseSide seq index x).add (← parseSide seq index y)
  | `($x - $y) => return (← parseSide seq index x).add ((← parseSide seq index y).scale (-1))
  | `(-$x) => return (← parseSide seq index x).scale (-1)
  | `($x * $y) =>
      let px ← parseSide seq index x
      let py ← parseSide seq index y
      if px.coefficients.isEmpty && py.coefficients.isEmpty then
        inTermsOfIndex index stx
      else if py.coefficients.isEmpty then
        match constantPart? py with
        | some c => return px.scale c
        | none => coefficient y x (surfaceText y)
      else if px.coefficients.isEmpty then
        match constantPart? px with
        | some c => return py.scale c
        | none => coefficient x y (surfaceText x)
      else linear stx
  | `($x / $y) =>
      let px ← parseSide seq index x
      let py ← parseSide seq index y
      if !py.coefficients.isEmpty then linear stx
      else if px.coefficients.isEmpty then inTermsOfIndex index stx
      else
        match constantPart? py with
        | some c =>
            if c = 0 then throwErrorAt stx "rsolve: division by zero"
            else return px.scale (1 / c)
        | none => coefficient y x s!"1 / {surfaceText y}"
  | _ => inTermsOfIndex index stx

/-! ## Solving -/

/-- The recurrence in normal form: `∑ cⱼ a (n + j) = g n` with `c_d ≠ 0`, `g` as `∑ rⁿ P (n)`. -/
structure Recurrence where
  /-- The order. -/
  order : Nat
  /-- The coefficients `c₀, …, c_d`. -/
  coefficients : Array ℚ
  /-- The right side `∑ rⁿ P (n)`. -/
  rhs : Sum.GeoPoly

/-- The value of `∑ cⱼ y (n + j)` at `n`. -/
def applyRecurrence (rec : Recurrence) (y : Nat → ℚ) (n : Nat) : ℚ :=
  (List.range (rec.order + 1)).foldl (fun acc j ↦ acc + rec.coefficients[j]! * y (n + j)) 0

/-- Solve a square rational linear system, `none` when singular. -/
def solve (M : QMatrix) (b : Array ℚ) : Option (Array ℚ) := do
  let inverse ← M.inverse?
  return inverse.mulVec b

/-- A particular solution `∑ C nᵗ rⁿ` of `∑ cⱼ a (n + j) = ∑ rⁿ P (n)` by undetermined
coefficients, as triples `(C, t, r)`. -/
def particular (rec : Recurrence) : Option (List (ℚ × Nat × ℚ)) := do
  let χ : Dense := rec.coefficients
  let mut out : List (ℚ × Nat × ℚ) := []
  for (r, P) in rec.rhs do
    let q := P.size
    if q = 0 then continue
    -- The multiplicity of `r` as a root of `χ`.
    let mut μ := 0
    let mut current := χ
    while current.size > 1 && Dense.eval current r == 0 do
      current := (Dense.divMod current #[-r, 1]).1
      μ := μ + 1
    -- Unknowns `e_t`, `t < q`, for `y n = n ^ (μ + t) rⁿ`; equations at `n = 0, …, q - 1`.
    let M : QMatrix := Array.ofFn fun (i : Fin q) ↦ Array.ofFn fun (t : Fin q) ↦
      applyRecurrence rec (fun m ↦ (m : ℚ) ^ (μ + (t : Nat)) * r ^ m) i
    let b : Array ℚ := Array.ofFn fun (i : Fin q) ↦ r ^ (i : Nat) * Algebra.Dense.eval P i
    let e ← solve M b
    for t in [0:q] do
      out := out ++ [(e[t]!, μ + t, r)]
  return out

/-- The value of the particular solution at `j`. -/
def particularValue (p : List (ℚ × Nat × ℚ)) (j : Nat) : ℚ :=
  p.foldl (fun acc (c, t, r) ↦ acc + c * (j : ℚ) ^ t * r ^ j) 0

/-- Read `a k = v` with `k` a natural number and `v` a rational. -/
def parseInitial (seq : Name) (stx : Syntax) : CommandElabM (Nat × ℚ) := do
  match stx with
  | `($f:ident $k:num = $v:term) =>
      unless f.getId == seq do throwErrorAt stx "rsolve: expected an initial value {seq} k = v"
      return (k.getNat, ← parseRationalLiteralFor "rsolve"
        "an initial value must be an exact rational literal, such as 2, -1/3 or 0.5" v)
  | _ => throwErrorAt stx "rsolve: expected an initial value {seq} k = v"

/-- The value `v` of an initial value `a k = v`, as written. -/
def initialValue (stx : Syntax) : CommandElabM (TSyntax `term) := do
  match stx with
  | `($_:ident $_:num = $v:term) => return v
  | _ => throwErrorAt stx "rsolve: expected an initial value a k = v"

/-- `(u, v)` with `(α + β) ^ N = u + v β` when `β ^ 2 = q`, as `LinearRecurrence.quadUV`. -/
def quadPow (α q : ℚ) (N : Nat) : ℚ × ℚ := Id.run do
  let mut p : ℚ × ℚ := (1, 0)
  for _ in [0:N] do
    p := (α * p.1 + q * p.2, p.1 + α * p.2)
  return p

/-- `X ^ k`. -/
def monomial (k : Nat) : Dense := (Array.replicate k (0 : ℚ)).push 1

/-- The quotient and the remainder of `G R' X ^ N` by `R`: the coefficient of `X ^ (deg R - 1)`
of the remainder is the value at `N` of `LinearRecurrence.encSeq R D G`. -/
def encDivision (R G : Dense) (N : Nat) : Dense × Dense :=
  Dense.divMod (Dense.mul (Dense.mul G (Dense.derivative R)) (monomial N)) R

/-! ## Terms -/

/-- The term `(q : ℝ)`. -/
def realQ (q : ℚ) : TermElabM (TSyntax `term) := do
  `(($(← ratSyntax q) : ℝ))

/-- `±t₁ ± t₂ ± ⋯` for terms with their signs (`true` for minus), `0` for no term. -/
def signedSum (terms : List (Bool × TSyntax `term)) : TermElabM (TSyntax `term) := do
  match terms with
  | [] => `((0 : ℝ))
  | (negative, first) :: rest =>
      let mut out ← if negative then `(-$first) else pure first
      for (negative, term) in rest do
        out ← if negative then `($out - $term) else `($out + $term)
      return out

/-- The sum of the terms, `0` for no term. -/
def plainSum (terms : Array (TSyntax `term)) : TermElabM (TSyntax `term) := do
  match terms.toList with
  | [] => `((0 : ℝ))
  | first :: rest => rest.foldlM (fun acc term ↦ `($acc + $term)) first

/-- The product of the factors present, `none` for no factor. -/
def product (factors : List (Option (TSyntax `term))) : TermElabM (Option (TSyntax `term)) := do
  match factors.filterMap id with
  | [] => return none
  | first :: rest => return some (← rest.foldlM (fun acc f ↦ `($acc * $f)) first)

/-- `c * body` as a sign and a magnitude, `|c|` alone without a body. -/
def scaled (c : ℚ) (body : Option (TSyntax `term)) : TermElabM (Bool × TSyntax `term) := do
  let magnitude ← realQ (if c < 0 then -c else c)
  match body with
  | none => return (decide (c < 0), magnitude)
  | some b =>
      if c = 1 ∨ c = -1 then return (decide (c < 0), b)
      else return (decide (c < 0), ← `($magnitude * $b))

/-- `(t : ℝ) ^ j`, `none` for `j = 0`. -/
def nPow (t : TSyntax `term) (j : Nat) : TermElabM (Option (TSyntax `term)) := do
  if j = 0 then return none
  if j = 1 then return some (← `((($t : ℕ) : ℝ)))
  return some (← `((($t : ℕ) : ℝ) ^ $(Syntax.mkNumLit (toString j))))

/-- `(r : ℝ) ^ t`, `none` for `r = 1`. -/
def rPow (r : ℚ) (t : TSyntax `term) : TermElabM (Option (TSyntax `term)) := do
  if r = 1 then return none
  return some (← `($(← realQ r) ^ $t))

/-- The terms `C nᵗ rⁿ` of a particular solution, at the index `t`. -/
def ypTerms (part : List (ℚ × Nat × ℚ)) (t : TSyntax `term) :
    TermElabM (List (Bool × TSyntax `term)) :=
  (part.filter (·.1 ≠ 0)).mapM fun (C, j, r) ↦ do
    scaled C (← product [← nPow t j, ← rPow r t])

/-- The right side `∑ rⁿ P (n) / c` of the monic recurrence, at the index `t`. -/
def rhsTerm (g : Sum.GeoPoly) (c : ℚ) (t : TSyntax `term) : TermElabM (TSyntax `term) := do
  let tR ← `((($t : ℕ) : ℝ))
  let mut terms : Array (TSyntax `term) := #[]
  for (r, P) in g do
    let P := P.map (· / c)
    unless P.any (· ≠ 0) do continue
    let poly ← polySyntax P.toList tR (← `(ℝ))
    match ← rPow r t with
    | none => terms := terms.push poly
    | some power => terms := terms.push (← `(($poly) * $power))
  plainSum terms

/-- `(A ± C √m) / den` for `α ± c √m`, with `A = α den` and `C = c den` integers. -/
def surdSyntax (α c m : ℚ) (plus : Bool) : TermElabM (TSyntax `term) := do
  let den : ℚ := ((Nat.lcm α.den c.den : ℕ) : ℚ)
  let AT ← realQ (α * den)
  let CT ← realQ (c * den)
  let root ← `(Real.sqrt $(← realQ m))
  let surd ← if c * den = 1 then pure root else `($CT * $root)
  let numerator ← if α = 0 then (if plus then pure surd else `(-$surd))
    else if plus then `($AT + $surd) else `($AT - $surd)
  if den = 1 then return numerator else `(($numerator) / $(← realQ den))

/-- `(A + C √m i) / den` for `α + c √m i`, with `A = α den` and `C = c den` integers. -/
def pairSyntax (α c m : ℚ) : TermElabM (TSyntax `term) := do
  let den : ℚ := ((Nat.lcm α.den c.den : ℕ) : ℚ)
  let CT ← `(($(← ratSyntax (c * den)) : ℂ))
  let imaginary ← if m = 1 then
      (if c * den = 1 then `(Complex.I) else `($CT * Complex.I))
    else do
      let s ← `(((Real.sqrt $(← realQ m) : ℝ) : ℂ))
      if c * den = 1 then `($s * Complex.I) else `($CT * $s * Complex.I)
  let numerator ← if α = 0 then pure imaginary
    else `(($(← ratSyntax (α * den)) : ℂ) + $imaginary)
  if den = 1 then return numerator else `(($numerator) / ($(← ratSyntax den) : ℂ))

/-- `α + c √m i` as `LinearRecurrence.charSeqs` writes it. -/
def zInternal (α c m : ℚ) : TermElabM (TSyntax `term) := do
  `((((($(← ratQ α) : ℚ) : ℝ) : ℂ) +
    ((LinearODE.CharRoot.width $(← ratQ c) $(← ratQ m) : ℝ) : ℂ) * Complex.I))

/-- A proof of `α + c √m i = z` for `z` as `pairSyntax` shows it. -/
def pairHz (α c m : ℚ) : TermElabM (TSyntax `term) := do
  let statement ← `($(← zInternal α c m) = $(← pairSyntax α c m))
  let proof ← if m = 1 then
      `(by
        simp only [LinearODE.CharRoot.width]
        push_cast
        simp only [Real.sqrt_one, Complex.ofReal_one]
        ring)
    else
      `(by
        simp only [LinearODE.CharRoot.width]
        push_cast
        ring)
  exprToSyntax (← elabCheckedProof "rsolve" statement proof)

/-- The bodies of `LinearRecurrence.charSeqs ρ j` at the index `t`. -/
def charSeqTerms (ρ : CharRoot) (j : Nat) (t : TSyntax `term) :
    TermElabM (Array (TSyntax `term)) := do
  let power ← `((($t : ℕ) : ℝ) ^ $(Syntax.mkNumLit (toString j)))
  match ρ with
  | .real r => return #[← `($power * ((($(← ratQ r) : ℚ) : ℝ)) ^ $t)]
  | .realPair α c m =>
      let αR ← `((($(← ratQ α) : ℚ) : ℝ))
      let w ← `(LinearODE.CharRoot.width $(← ratQ c) $(← ratQ m))
      return #[← `($power * ($αR + $w) ^ $t), ← `($power * ($αR - $w) ^ $t)]
  | .pair α c m =>
      let z ← zInternal α c m
      return #[← `($power * (($z) ^ $t).re), ← `($power * (($z) ^ $t).im)]

/-- The functions of `charSeqs ρ j` at the index `t` as shown (`none` for `1`). -/
def charSeqShown (ρ : CharRoot) (j : Nat) (t : TSyntax `term) :
    TermElabM (Array (Option (TSyntax `term))) := do
  let power ← nPow t j
  match ρ with
  | .real r => return #[← product [power, ← rPow r t]]
  | .realPair α c m =>
      let plus ← `(($(← surdSyntax α c m true)) ^ $t)
      let minus ← `(($(← surdSyntax α c m false)) ^ $t)
      return #[← product [power, some plus], ← product [power, some minus]]
  | .pair α c m =>
      let z ← pairSyntax α c m
      return #[← product [power, some (← `((($z) ^ $t).re))],
        ← product [power, some (← `((($z) ^ $t).im))]]

/-- A solution of the exact part used for initial values: `nʲ rⁿ`, and for a pair of roots
`nʲ (r₊ⁿ + r₋ⁿ)` and `nʲ (r₊ⁿ - r₋ⁿ) / √m`, or `nʲ Re zⁿ` and `nʲ Im zⁿ / √m`. -/
structure ExactSeq where
  /-- The position of the root among the exact roots. -/
  index : Nat
  /-- The root. -/
  root : CharRoot
  /-- The power of `n`. -/
  j : Nat
  /-- Whether this is the second solution of a pair. -/
  second : Bool

/-- The solutions of the exact roots, root by root and power by power. -/
def exactSeqs (exact : List (CharRoot × Nat)) : Array ExactSeq := Id.run do
  let mut out : Array ExactSeq := #[]
  for ((ρ, k), i) in exact.zipIdx do
    for j in [0:k] do
      out := out.push ⟨i, ρ, j, false⟩
      unless ρ matches .real _ do out := out.push ⟨i, ρ, j, true⟩
  return out

/-- The value at `N`, a rational number. -/
def ExactSeq.value (s : ExactSeq) (N : Nat) : ℚ :=
  let power : ℚ := (N : ℚ) ^ s.j
  match s.root with
  | .real r => power * r ^ N
  | .realPair α c m =>
      let (u, v) := quadPow α (c ^ 2 * m) N
      if s.second then power * (2 * (c * v)) else power * (2 * u)
  | .pair α c m =>
      let (u, v) := quadPow α (-(c ^ 2 * m)) N
      if s.second then power * (c * v) else power * u

/-- The solution at the index `t` without the power of `n`, as the lemmas of
`LinearRecurrence` write it. -/
def ExactSeq.core (s : ExactSeq) (t : TSyntax `term) : TermElabM (TSyntax `term) := do
  match s.root with
  | .real r => `(((($(← ratQ r) : ℚ) : ℝ)) ^ $t)
  | .realPair α c m =>
      let αR ← `((($(← ratQ α) : ℚ) : ℝ))
      let w ← `(LinearODE.CharRoot.width $(← ratQ c) $(← ratQ m))
      let sqrt ← `(Real.sqrt ((($(← ratQ m) : ℚ) : ℝ)))
      if s.second then `((($αR + $w) ^ $t - ($αR - $w) ^ $t) / $sqrt)
      else `(($αR + $w) ^ $t + ($αR - $w) ^ $t)
  | .pair α c m =>
      let z ← zInternal α c m
      let sqrt ← `(Real.sqrt ((($(← ratQ m) : ℚ) : ℝ)))
      if s.second then `((($z) ^ $t).im / $sqrt) else `((($z) ^ $t).re)

/-- The solution at the index `t`, as the lemmas of `LinearRecurrence` write it. -/
def ExactSeq.internal (s : ExactSeq) (t : TSyntax `term) : TermElabM (TSyntax `term) := do
  let core ← s.core t
  match ← nPow t s.j with
  | none => return core
  | some power => `($power * ($core))

/-- The solution at the index `t` as shown (`none` for `1`). -/
def ExactSeq.shown (s : ExactSeq) (t : TSyntax `term) : TermElabM (Option (TSyntax `term)) := do
  let power ← nPow t s.j
  match s.root with
  | .real r => product [power, ← rPow r t]
  | .realPair α c m =>
      let plus ← `(($(← surdSyntax α c m true)) ^ $t)
      let minus ← `(($(← surdSyntax α c m false)) ^ $t)
      if s.second then product [power, some (← `(($plus - $minus) / Real.sqrt $(← realQ m)))]
      else product [power, some (← `($plus + $minus))]
  | .pair α c m =>
      let z ← pairSyntax α c m
      if s.second then
        if m = 1 then product [power, some (← `((($z) ^ $t).im))]
        else product [power, some (← `((($z) ^ $t).im / Real.sqrt $(← realQ m)))]
      else product [power, some (← `((($z) ^ $t).re))]

/-- `∑ wᵢ sᵢ` at the index `t` over the nonzero weights, as the lemmas write it. -/
def eSum (seqs : Array ExactSeq) (weights : Array ℚ) (t : TSyntax `term) :
    TermElabM (TSyntax `term) := do
  let mut terms : Array (TSyntax `term) := #[]
  for (s, w) in seqs.zip weights do
    if w ≠ 0 then terms := terms.push (← `($(← realQ w) * ($(← s.internal t))))
  plainSum terms

/-- The tactics in sequence. -/
def seqTactic (steps : Array (TSyntax `tactic)) : TermElabM (TSyntax `tactic) := do
  let mut out := steps[0]!
  for step in steps.extract 1 steps.size do
    out ← `(tactic| ($out; $step))
  return out

/-! ## Theorems -/

/-- `simp only [lemmas] at h ⊢`, or `simp only [lemmas]` without `h`. -/
def simpAt (lemmas : Array (TSyntax `term)) (h? : Option (TSyntax `ident)) :
    TermElabM (TSyntax `tactic) := do
  let simpArgs : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ←
    lemmas.mapM fun l ↦ `(Lean.Parser.Tactic.simpLemma| $l:term)
  let args : Syntax.TSepArray [``Lean.Parser.Tactic.simpStar,
      ``Lean.Parser.Tactic.simpErase, ``Lean.Parser.Tactic.simpLemma] "," :=
    .ofElems (simpArgs.map fun l ↦ ⟨l.raw⟩)
  match h? with
  | some h => `(tactic| simp only [$args,*] at $h:ident ⊢)
  | none => `(tactic| simp only [$args,*])

/-- A proof of `α ± c √m = s` for `s` as `surdSyntax` shows it. -/
def surdEq (α c m : ℚ) (plus : Bool) : TermElabM (TSyntax `term) := do
  let αR ← `((($(← ratQ α) : ℚ) : ℝ))
  let w ← `(LinearODE.CharRoot.width $(← ratQ c) $(← ratQ m))
  let root ← if plus then `($αR + $w) else `($αR - $w)
  let statement ← `($root = $(← surdSyntax α c m plus))
  -- `push_cast` leaves a goal for `ring`, as in `pairHz`.
  let proof ← `(by
    simp only [LinearODE.CharRoot.width]
    push_cast
    ring)
  exprToSyntax (← elabCheckedProof "rsolve" statement proof)

/-- The equations from the roots as `LinearRecurrence` writes them to the roots as shown:
`surdEq` for a pair of real roots, `pairHz` for a pair of complex roots and `Complex.re_add_im`
for the enclosed complex roots. -/
def shownEqs (roots : RootSplit.Roots) : TermElabM (Array (TSyntax `term)) := do
  let mut out : Array (TSyntax `term) := #[]
  for (ρ, _) in roots.split.exact do
    match ρ with
    | .real _ => pure ()
    | .realPair α c m => out := (out.push (← surdEq α c m true)).push (← surdEq α c m false)
    | .pair α c m => out := out.push (← pairHz α c m)
  unless roots.D.discs.isEmpty do out := out.push (← `(Complex.re_add_im))
  return out

/-- `⟨mp, mpr⟩` between an equation as `LinearRecurrence` writes it and the same equation as
shown: `simp only` with `shownEqs`, `push_cast`, then `linear_combination`. -/
def stepIff (eqs : Array (TSyntax `term)) : TermElabM (TSyntax `term) := do
  let h ← hygienicIdent `h
  let one ← if eqs.isEmpty then
      `(fun $h:ident ↦ by
        push_cast at $h:ident ⊢
        linear_combination $h:ident)
    else
      let simpT ← simpAt eqs (some h)
      `(fun $h:ident ↦ by
        $simpT:tactic
        push_cast at $h:ident ⊢
        linear_combination $h:ident)
  `(⟨$one, $one⟩)

/-- The functions of `seqBasis (combined rs R D)`: as `LinearRecurrence` writes them, as
functions of `m`, and as shown at the index `t` (`none` for `1`). -/
def basisParts (roots : RootSplit.Roots) (RT t : TSyntax `term) :
    TermElabM (Array (TSyntax `term) × Array (Option (TSyntax `term))) := do
  let m ← hygienicIdent `m
  let mT : TSyntax `term := ⟨m.raw⟩
  let mut internal : Array (TSyntax `term) := #[]
  let mut shown : Array (Option (TSyntax `term)) := #[]
  for (ρ, k) in roots.split.exact do
    for j in [0:k] do
      for body in ← charSeqTerms ρ j mT do
        internal := internal.push (← `(fun $m:ident : ℕ ↦ $body))
      shown := shown ++ (← charSeqShown ρ j t)
  for (lo, hi) in roots.D.reals do
    let r ← `(AlgRoot.real $RT $(← boundQ lo) $(← boundQ hi))
    internal := internal.push (← `(fun $m:ident : ℕ ↦ (($mT : ℕ) : ℝ) ^ 0 * $r ^ $mT))
    shown := shown.push (some (← `($r ^ $t)))
  for (u, v, ρ, _) in roots.D.discs do
    let z ← `(AlgRoot.complex $RT $(← boundQ u) $(← boundQ v) $(← boundQ ρ))
    let w ← `((((($z).re : ℝ) : ℂ) + ((($z).im : ℝ) : ℂ) * Complex.I) ^ $mT)
    internal := internal.push (← `(fun $m:ident : ℕ ↦ (($mT : ℕ) : ℝ) ^ 0 * ($w).re))
    internal := internal.push (← `(fun $m:ident : ℕ ↦ (($mT : ℕ) : ℝ) ^ 0 * ($w).im))
    shown := (shown.push (some (← `((($z) ^ $t).re)))).push (some (← `((($z) ^ $t).im)))
  return (internal, shown)

/-- The proofs shared by the two theorems: the bridge
`∀ a, (∀ n, eq) ↔ ∀ n, sLop d A a n = F n` from the recurrence as written to the monic one, and
the particular solution `∀ n, sLop d A Yp n = F n`, with `Yp` as a function of `m`. -/
def commonParts (rec : Recurrence) (part : List (ℚ × Nat × ℚ)) (t : RootTerms)
    (aI nI : TSyntax `ident) (equation : TSyntax `term) :
    TermElabM (TSyntax `term × TSyntax `term) := do
  let aT : TSyntax `term := ⟨aI.raw⟩
  let nT : TSyntax `term := ⟨nI.raw⟩
  let A := t.a
  let dT := t.d
  let top := rec.coefficients[rec.order]!
  let topT ← realQ top
  let k ← hygienicIdent `k
  let m ← hygienicIdent `m
  let coefficients ← `(fun $k:ident ↦ ((($A : List ℚ).getD $k 0 : ℚ) : ℝ))
  let F ← rhsTerm rec.rhs top nT
  let Yp ← `(fun $m:ident : ℕ ↦ $(← signedSum (← ypTerms part ⟨m.raw⟩)))
  let sumSimp ← `(tactic| simp only [LinearRecurrence.sLop, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add, add_zero, List.getD_cons_zero, List.getD_cons_succ])
  let bridgeStatement ← `(∀ $aI:ident : ℕ → ℝ, (∀ $nI:ident : ℕ, $equation) ↔
    ∀ $nI:ident : ℕ, LinearRecurrence.sLop $dT $coefficients $aT $nT = $F)
  let bridgeProof ← `(by
    intro $aI:ident
    apply forall_congr'
    intro $nI:ident
    $sumSimp:tactic
    push_cast
    constructor
    · intro h
      linear_combination (1 / $topT) * h
    · intro h
      linear_combination ($topT : ℝ) * h)
  let bridge ← exprToSyntax (← elabCheckedProof "rsolve" bridgeStatement bridgeProof)
  let partStatement ← `(∀ $nI:ident : ℕ, LinearRecurrence.sLop $dT $coefficients $Yp $nT = $F)
  -- `push_cast` then `ring` close `∑ₖ Aₖ Yp (n + k) = F n`, as in DSolveRoot.
  let partProof ← if (← ypTerms part nT).isEmpty then
      `(by
        intro $nI:ident
        simp only [LinearRecurrence.sLop, mul_zero, Finset.sum_const_zero])
    else
      `(by
        intro $nI:ident
        $sumSimp:tactic
        push_cast
        ring)
  let partT ← exprToSyntax (← elabCheckedProof "rsolve" partStatement partProof)
  return (bridge, partT)

/-- `c₁, …, c_k`. -/
def cIdents (k : Nat) : Array (TSyntax `ident) :=
  (Array.range k).map fun i ↦ mkIdent (Name.mkSimple s!"c{Nat.toSubscriptString (i + 1)}")

/-- The statement with the enclosures of the roots without closed form as conjuncts before
`body`, and its proof from the proofs of the enclosures and the proof of `body`. -/
def withEnclosures (roots : RootSplit.Roots) (RT body proof : TSyntax `term) :
    TermElabM (TSyntax `term × TSyntax `term) := do
  let (statements, proofs) ← enclosureParts roots.R roots.D RT
  let statement ← statements.foldrM (fun e acc ↦ `($e ∧ $acc)) body
  if proofs.isEmpty then return (statement, proof)
  return (statement, ← `(⟨$proofs,*, $proof⟩))

/-- The theorem with its enclosed roots named by `let`, and its proof. -/
def finish (statement proof : TSyntax `term) : TermElabM (Lean.Expr × Lean.Expr) := do
  let value ← elabCheckedProof "rsolve" statement proof
  let type ← instantiateMVars (← inferType value)
  let named ← letRoots type
  return (named, ← mkExpectedTypeHint value named)

/-- The general solution `∀ a, (∀ n, eq) ↔ ∃ c₁ …, ∀ n, a n = Yp n + c₁ φ₁ n + ⋯`, after the
enclosures of the roots without closed form, with its proof from `rec_general`. -/
def generalTheorem (rec : Recurrence) (part : List (ℚ × Nat × ℚ)) (roots : RootSplit.Roots)
    (aI nI : TSyntax `ident) (equation : TSyntax `term) : TermElabM (Lean.Expr × Lean.Expr) := do
  let aT : TSyntax `term := ⟨aI.raw⟩
  let nT : TSyntax `term := ⟨nI.raw⟩
  let t ← roots.terms
  let (bridge, partT) ← commonParts rec part t aI nI equation
  let (internal, shown) ← basisParts roots t.R nT
  let cs := cIdents internal.size
  let mut terms ← ypTerms part nT
  for (c, φ) in cs.zip shown do
    let cT : TSyntax `term := ⟨c.raw⟩
    let term ← match φ with
      | none => pure cT
      | some φ => `($cT * $φ)
    terms := terms ++ [(false, term)]
  let mut exists_ ← `(∀ $nI:ident : ℕ, $aT $nT = $(← signedSum terms))
  for c in cs.reverse do
    exists_ ← `(∃ $c:ident : ℝ, $exists_)
  let general ← `(∀ $aI:ident : ℕ → ℝ, (∀ $nI:ident : ℕ, $equation) ↔ $exists_)
  let mut conv ← `(forall_congr' fun $nI:ident ↦ $(← stepIff (← shownEqs roots)))
  for c in cs.reverse do
    conv ← `(exists_congr fun $c:ident ↦ $conv)
  -- `rfl` unfolds `seqBasis (combined rs R D)` to these functions, as the
  -- `rrBasis` step of DSolveRoot.
  let hbasis ← `((show LinearRecurrence.seqBasis $(t.all) = $(← listSyntax internal) by rfl))
  let ha0 ← certified (← `((($(t.a) : List ℚ)).getD 0 0 ≠ 0))
  let body ← `(fun $aI:ident ↦ by
    rw [$bridge $aT, LinearRecurrence.rec_general $(t.rs) $(t.hv) $(t.hsep) $(t.hpos) $(t.R)
      $(t.D) $(t.hD) $(t.U) $(t.V) $(t.hb) $(t.a) $(t.hA) $(t.hlen) $ha0 $partT (y := $aT),
      $hbasis:term]
    simp only [LinearODE.mem_span_cons_iff, LinearODE.mem_span_nil_iff]
    exact $conv)
  let (statement, proof) ← withEnclosures roots t.R general body
  finish statement proof

/-! ## Initial values -/

/-- A proof that `√m` as `ExactSeq.core` writes it equals `√m` as shown, `1` for `m = 1`. -/
def sqrtEq (m : ℚ) : TermElabM (TSyntax `term) := do
  let rhs ← if m = 1 then `((1 : ℝ)) else `(Real.sqrt $(← realQ m))
  let statement ← `(Real.sqrt ((($(← ratQ m) : ℚ) : ℝ)) = $rhs)
  exprToSyntax (← elabCheckedProof "rsolve" statement (← `(by norm_num)))

/-- The value at `N` of `LinearRecurrence.encSeq R D G`, as `encSeq_eq` gives it. -/
def encValue (R G : Dense) (N : Nat) : ℚ :=
  (encDivision R G N).2.getD (R.size - 2) 0

/-- The weights of `exactSeqs` and the polynomial `G` over the enclosed roots for the values
`v k` at `k₀ + k`, `k < d`: a square rational linear system. -/
def ivpWeights (roots : RootSplit.Roots) (part : List (ℚ × Nat × ℚ)) (seqs : Array ExactSeq)
    (k₀ : Nat) (values : Array ℚ) : Option (Array ℚ × Dense) := do
  let e := roots.R.size - 1
  let M : QMatrix := Array.ofFn fun (k : Fin values.size) ↦
    seqs.map (·.value (k₀ + k.val)) ++
      Array.ofFn fun (i : Fin e) ↦ encValue roots.R (monomial i.val) (k₀ + k.val)
  let b : Array ℚ := Array.ofFn fun (k : Fin values.size) ↦
    values[k.val]! - particularValue part (k₀ + k.val)
  let x ← solve M b
  return (x.extract 0 seqs.size, Dense.trim (x.extract seqs.size x.size))

/-- A proof of `Yp N + E N + encSeq R D G N = v`: `encSeq_eq` and the pair lemmas turn the left
side into rational numbers, which the kernel decides, and `norm_num` adds them. -/
def valueFact (roots : RootSplit.Roots) (t : RootTerms) (part : List (ℚ × Nat × ℚ))
    (seqs : Array ExactSeq) (weights : Array ℚ) (G : Dense) (N : Nat) (v : TSyntax `term) :
    TermElabM (TSyntax `term) := do
  let NT ← natLit N
  let GT ← `(($(← listSyntax (← G.mapM ratQ)) : List ℚ))
  let (T, Q) := encDivision roots.R G N
  let TT ← `(($(← listSyntax (← T.mapM ratQ)) : List ℚ))
  let QT ← `(($(← listSyntax (← Q.mapM ratQ)) : List ℚ))
  let hdiv ← certified (← `(CAS.Polynomial.coeffEq (CAS.Polynomial.coeffMul
      (CAS.Polynomial.coeffMul $GT (CAS.Polynomial.coeffDeriv $(t.R))) (LinearODE.powX $NT))
      (CAS.Polynomial.coeffAdd (CAS.Polynomial.coeffMul $TT $(t.R)) $QT)
      = true))
  let hQ ← certified (← `(($QT).length < ($(t.R)).length))
  let hq ← certified (← `(($QT).getD (($(t.R)).length - 2) 0 = $(← ratQ (encValue roots.R G N))))
  let mut rules : Array (TSyntax `term) :=
    #[← `(LinearRecurrence.encSeq_eq $(t.R) $(t.D) $(t.hD) $GT $TT $QT $NT $hdiv $hQ), hq]
  for ((ρ, _), i) in roots.split.exact.zipIdx do
    let used (second : Bool) : Bool := (seqs.zip weights).any fun (s, w) ↦
      s.index == i && s.second == second && w != 0
    let some (α, c, m, complex) := (match ρ with
        | .real _ => none
        | .realPair α c m => some (α, c, m, false)
        | .pair α c m => some (α, c, m, true)) | continue
    unless used false || used true do continue
    let αT ← ratQ α
    let cT ← ratQ c
    let mT ← ratQ m
    let qT ← if complex then `(-($cT ^ 2 * $mT)) else `($cT ^ 2 * $mT)
    let (u, w) := quadPow α (if complex then -(c ^ 2 * m) else c ^ 2 * m) N
    if used false then
      let hm ← certified (← `((0 : ℚ) ≤ $mT))
      rules := rules.push (← if complex then `(LinearRecurrence.pairC_re_eq $αT $cT $mT $hm $NT)
        else `(LinearRecurrence.pair_add_eq $αT $cT $mT $hm $NT))
    if used true then
      let hm ← certified (← `((0 : ℚ) < $mT))
      rules := rules.push (← if complex then `(LinearRecurrence.pairC_im_eq $αT $cT $mT $hm $NT)
        else `(LinearRecurrence.pair_sub_eq $αT $cT $mT $hm $NT))
    -- The kernel decides `quadUV` at `N` by evaluation.
    rules := rules.push
      (← certified (← `(LinearRecurrence.quadUV $αT ($qT) $NT = ($(← ratQ u), $(← ratQ w)))))
  let rwRules : Array (TSyntax ``Lean.Parser.Tactic.rwRule) ←
    rules.mapM fun r ↦ `(Lean.Parser.Tactic.rwRule| $r:term)
  let statement ← `($(← signedSum (← ypTerms part NT)) + $(← eSum seqs weights NT) +
    LinearRecurrence.encSeq $(t.R) $(t.D) $GT $NT = $v)
  -- `rw` finds the pair patterns of `ExactSeq.core`, `norm_num` adds the rest.
  let proof ← `(by
    rw [$rwRules,*]
    all_goals norm_num)
  exprToSyntax (← elabCheckedProof "rsolve" statement proof)

/-- A proof that `E = ∑ wᵢ sᵢ` lies in the span of the solutions of the exact roots: the
coefficients of `nʲ r₊ⁿ` and `nʲ r₋ⁿ` are `w ± w' / √m`, those of `nʲ Re zⁿ` and `nʲ Im zⁿ` are
`w` and `w' / √m`. -/
def spanFact (t : RootTerms) (seqs : Array ExactSeq) (weights : Array ℚ) (E : TSyntax `term) :
    TermElabM (TSyntax `term) := do
  let m ← hygienicIdent `m
  let mT : TSyntax `term := ⟨m.raw⟩
  let mut ψs : Array (TSyntax `term) := #[]
  let mut cs : Array (TSyntax `term) := #[]
  let mut k := 0
  while k < seqs.size do
    let some s := seqs[k]? | break
    let w₁ ← realQ weights[k]!
    let bodies ← charSeqTerms s.root s.j mT
    for body in bodies do
      ψs := ψs.push (← `(fun $m:ident : ℕ ↦ $body))
    match s.root with
    | .real _ =>
        cs := cs.push w₁
        k := k + 1
    | .realPair _ _ μ =>
        let w₂ ← `($(← realQ weights[k + 1]!) / Real.sqrt ((($(← ratQ μ) : ℚ) : ℝ)))
        cs := (cs.push (← `($w₁ + $w₂))).push (← `($w₁ - $w₂))
        k := k + 2
    | .pair _ _ μ =>
        let w₂ ← `($(← realQ weights[k + 1]!) / Real.sqrt ((($(← ratQ μ) : ℚ) : ℝ)))
        cs := (cs.push w₁).push w₂
        k := k + 2
  let exactRoots ← `(List.map (fun e ↦ (LinearODE.RRoot.char e.1, e.2))
      ($(t.rs) : List (LinearODE.CharRoot × ℕ)))
  let statement ←
    `($E ∈ Submodule.span ℝ {f | f ∈ LinearRecurrence.seqBasis $exactRoots})
  let n ← hygienicIdent `n
  -- `seqBasis` of the exact roots unfolds by `rfl` to the functions `ψs`, as `hbasis` of
  -- `generalTheorem`; `rw` with this equation keeps the unifier away from `Submodule.span`.
  let hbasis ← `((show LinearRecurrence.seqBasis $exactRoots = $(← listSyntax ψs) by rfl))
  let proof ← if ψs.isEmpty then `(zero_mem _) else `(by
    rw [$hbasis:term]
    simp only [LinearODE.mem_span_cons_iff, LinearODE.mem_span_nil_iff]
    exact ⟨$cs,*, fun $n:ident ↦ by ring⟩)
  exprToSyntax (← elabCheckedProof "rsolve" statement proof)

/-- The closed form `Y` at the index `n` as shown, with the proof of
`∀ n, Yp n + E n + encSeq R D G n = Y n`: the enclosed roots enter as `G(r) rⁿ` and
`2 Re (G(z) zⁿ)`. -/
def closedForm (roots : RootSplit.Roots) (t : RootTerms) (part : List (ℚ × Nat × ℚ))
    (seqs : Array ExactSeq) (weights : Array ℚ) (G : Dense) (nI : TSyntax `ident) :
    TermElabM (TSyntax `term × TSyntax `term) := do
  let nT : TSyntax `term := ⟨nI.raw⟩
  let GT ← `(($(← listSyntax (← G.mapM ratQ)) : List ℚ))
  let mut terms ← ypTerms part nT
  for (s, w) in seqs.zip weights do
    if w ≠ 0 then terms := terms ++ [← scaled w (← s.shown nT)]
  let mut eqs ← shownEqs roots
  for (ρ, _) in roots.split.exact do
    match ρ with
    | .realPair _ _ m | .pair _ _ m => eqs := eqs.push (← sqrtEq m)
    | .real _ => pure ()
  if G.isEmpty then
    eqs := eqs ++ #[← `(CAS.Polynomial.coeffEval_nil), ← `(AlgRoot.polyC_nil),
      ← `(AlgRoot.polyC_cons),
      ← `(_root_.Polynomial.eval_zero), ← `(zero_mul), ← `(mul_zero), ← `(Complex.zero_re)]
  else
    for (lo, hi) in roots.D.reals do
      let r ← `(AlgRoot.real $(t.R) $(← boundQ lo) $(← boundQ hi))
      let shown ← polySyntax G.toList r (← `(ℝ))
      let statement ← `(CAS.Polynomial.coeffEval $GT $r = $shown)
      let proof ← `(by
        simp only [CAS.Polynomial.coeffEval_cons, CAS.Polynomial.coeffEval_nil]
        push_cast
        ring)
      eqs := eqs.push (← exprToSyntax (← elabCheckedProof "rsolve" statement proof))
      terms := terms ++ [(false, ← `(($shown) * $r ^ $nT))]
    for (u, v, ρ, _) in roots.D.discs do
      let z ← `(AlgRoot.complex $(t.R) $(← boundQ u) $(← boundQ v) $(← boundQ ρ))
      let shown ← polySyntax G.toList z (← `(ℂ))
      let statement ← `(_root_.Polynomial.eval $z (AlgRoot.polyC $GT) = $shown)
      let proof ← `(by
        simp only [AlgRoot.polyC_cons, AlgRoot.polyC_nil, _root_.Polynomial.eval_add,
          _root_.Polynomial.eval_mul, _root_.Polynomial.eval_C, _root_.Polynomial.eval_X,
          _root_.Polynomial.eval_zero]
        push_cast
        ring)
      eqs := eqs.push (← exprToSyntax (← elabCheckedProof "rsolve" statement proof))
      terms := terms ++ [(false, ← `(2 * ((($shown) * ($z) ^ $nT).re)))]
  let Y ← signedSum terms
  let statement ← `(∀ $nI:ident : ℕ, $(← signedSum (← ypTerms part nT)) +
    $(← eSum seqs weights nT) + LinearRecurrence.encSeq $(t.R) $(t.D) $GT $nT = $Y)
  let unfold := #[← `(LinearRecurrence.encSeq), ← `(List.map_cons), ← `(List.map_nil),
    ← `(List.sum_cons), ← `(List.sum_nil)]
  let simpT ← simpAt (unfold ++ eqs) none
  -- `simp only` reduces the projections of the literal enclosures `D` and
  -- rewrites with `eqs`; `push_cast` and `ring` close the rest.
  let proof ← `(by
    intro $nI:ident
    $simpT:tactic
    push_cast
    ring)
  return (Y, ← exprToSyntax (← elabCheckedProof "rsolve" statement proof))

/-- The initial-value theorem `∀ a, ((∀ n, eq) ∧ a k₀ = v₀ ∧ ⋯) ↔ ∀ n, a n = Y n` for the
values `vₖ` at the `d` consecutive indices `k₀ + k`, after the enclosures of the roots without
closed form, with its proof from `rec_ivp`. -/
def ivpTheorem (rec : Recurrence) (part : List (ℚ × Nat × ℚ)) (roots : RootSplit.Roots)
    (aI nI : TSyntax `ident) (equation : TSyntax `term) (k₀ : Nat) (values : Array ℚ)
    (valueTerms : Array (TSyntax `term)) : TermElabM (Lean.Expr × Lean.Expr) := do
  let aT : TSyntax `term := ⟨aI.raw⟩
  let nT : TSyntax `term := ⟨nI.raw⟩
  let t ← roots.terms
  let (bridge, partT) ← commonParts rec part t aI nI equation
  let seqs := exactSeqs roots.split.exact
  let some (weights, G) := ivpWeights roots part seqs k₀ values
    | throwError "rsolve: the initial values do not determine a solution"
  let m ← hygienicIdent `m
  let E ← `(fun $m:ident : ℕ ↦ $(← eSum seqs weights ⟨m.raw⟩))
  let hE ← spanFact t seqs weights E
  let (Y, hY) ← closedForm roots t part seqs weights G nI
  let GT ← `(($(← listSyntax (← G.mapM ratQ)) : List ℚ))
  let k₀T ← natLit k₀
  let k ← hygienicIdent `k
  let kT : TSyntax `term := ⟨k.raw⟩
  let hk ← hygienicIdent `hk
  let h ← hygienicIdent `h
  let hT : TSyntax `term := ⟨h.raw⟩
  let vfun ← `(fun $k:ident : ℕ ↦ ($(← listSyntax valueTerms) : List ℝ).getD $kT 0)
  -- The values `Yp N + E N + encSeq R D G N = vₖ` at `N = k₀ + k`, then `hval` by cases on `k`.
  let mut exacts : Array (TSyntax `tactic) := #[← `(tactic| interval_cases $k:ident)]
  for (v, i) in valueTerms.zipIdx do
    let fact ← valueFact roots t part seqs weights G (k₀ + i) v
    exacts := exacts.push (← `(tactic| exact $fact))
  let idx ← `($k₀T + $kT)
  let hvalStatement ← `(∀ $k:ident : ℕ, $kT < $(t.d) → $(← signedSum (← ypTerms part idx)) +
    $(← eSum seqs weights idx) + LinearRecurrence.encSeq $(t.R) $(t.D) $GT ($idx) = $vfun $kT)
  -- After `interval_cases k` each goal is the value fact up to `k₀ + i = N`
  -- and `List.getD`, which `exact` unfolds.
  let hval ← exprToSyntax (← elabCheckedProof "rsolve" hvalStatement (← `(by
    intro $k:ident $hk:ident
    $(← seqTactic exacts):tactic)))
  -- `a k₀ = v₀ ∧ ⋯ ↔ ∀ k < d, a (k₀ + k) = v k`.
  let d := valueTerms.size
  let conjuncts ← valueTerms.zipIdx.mapM fun (v, i) ↦ do
    `($aT $(← natLit (k₀ + i)) = $v)
  let conj ← conjuncts.pop.foldrM (fun c acc ↦ `($c ∧ $acc)) conjuncts.back!
  let mut picks : Array (TSyntax `tactic) := #[← `(tactic| interval_cases $k:ident)]
  for i in [0:d] do
    let mut p := hT
    for _ in [0:i] do p ← `(And.right $p)
    if i + 1 < d then p ← `(And.left $p)
    picks := picks.push (← `(tactic| exact $p))
  let parts ← (Array.range d).mapM fun i ↦ do `($hT $(← natLit i) (by norm_num))
  let back ← if d = 1 then pure parts[0]! else `(⟨$parts,*⟩)
  let initStatement ← `(∀ $aI:ident : ℕ → ℝ,
    $conj ↔ ∀ $k:ident : ℕ, $kT < $(t.d) → $aT ($k₀T + $kT) = $vfun $kT)
  let init ← exprToSyntax (← elabCheckedProof "rsolve" initStatement (← `(by
    intro $aI:ident
    constructor
    · intro $h:ident $k:ident $hk:ident
      $(← seqTactic picks):tactic
    · intro $h:ident
      exact $back)))
  let ha ← certified (← `((($(t.a) : List ℚ)).getD $(t.d) 0 = 1))
  let ha0 ← certified (← `((($(t.a) : List ℚ)).getD 0 0 ≠ 0))
  let statementBody ← `(∀ $aI:ident : ℕ → ℝ,
    ((∀ $nI:ident : ℕ, $equation) ∧ $conj) ↔ ∀ $nI:ident : ℕ, $aT $nT = $Y)
  let body ← `(fun $aI:ident ↦ (and_congr ($bridge $aT) ($init $aT)).trans
    (LinearRecurrence.rec_ivp $(t.rs) $(t.hv) $(t.hsep) $(t.hpos) $(t.R) $(t.D) $(t.hD) $(t.U)
      $(t.V) $(t.hb) $(t.a) $(t.hA) $(t.hlen) $ha $ha0 $partT $GT $hE $k₀T $vfun $hval $hY
      (y := $aT)))
  let (statement, proof) ← withEnclosures roots t.R statementBody body
  finish statement proof

/-! ## The command -/

/-- Run `#cas [rsolve a n, a k₀ = v₀, …] equation`: read the recurrence, split its characteristic
polynomial with `RootSplit.rootsHere`, and prove the general solution or, with initial values at
`d` consecutive indices, the solution with these values. -/
def logRSolve (ref : Syntax) (seqId indexId : TSyntax `ident) (initialStx : Array Syntax)
    (equation : Syntax) : CommandElabM Unit := do
  let seq := seqId.getId
  let index := indexId.getId
  let equation := LinearAlgebra.unparen equation
  let (lhs, rhs) ← match equation with
    | `($l = $r) => pure (l, r)
    | _ => throwErrorAt equation "rsolve: expected an equation"
  let total := (← parseSide seq index lhs).add ((← parseSide seq index rhs).scale (-1))
  let coefficients := total.coefficients.filter (·.2 ≠ 0)
  if coefficients.isEmpty then throwErrorAt equation "rsolve: the equation does not involve {seq}"
  let minShift := coefficients.foldl (fun m (j, _) ↦ min m j) (coefficients.head!.1)
  unless minShift = 0 do
    throwErrorAt equation "rsolve: the coefficient of {seq} {index} is zero; this is a \
      recurrence of lower order for {seq} ({index} + {minShift})"
  let order := coefficients.foldl (fun m (j, _) ↦ max m j) 0
  if order = 0 then
    throwErrorAt equation "rsolve: the equation involves {seq} {index} only, not a shift \
      {seq} ({index} + k)"
  let coefficientArray : Array ℚ := Array.ofFn fun (j : Fin (order + 1)) ↦
    (coefficients.find? (·.1 == (j : Nat))).map (·.2) |>.getD 0
  -- `∑ cⱼ a (n + j) + ρ (n) = 0`, so the right side is `g = -ρ`.
  let g : Sum.GeoPoly ← match total.rest with
    | none => pure []
    | some ρ => match Sum.toGeoPoly ρ with
        | some geo => pure (Sum.gScale (-1) geo)
        | none => throwErrorAt equation
            "rsolve: the terms in {index} must be sums of c {index}^j r^{index}"
  let rec_ : Recurrence := { order, coefficients := coefficientArray, rhs := g }
  let some part := particular rec_
    | throwErrorAt equation "rsolve: no particular solution found by undetermined coefficients"
  let roots ← match ← RootSplit.rootsHere coefficientArray with
    | .ok roots => pure roots
    | .error message => throwErrorAt equation "rsolve: {message}"
  let initial ← initialStx.mapM (parseInitial seq)
  let valueTerms ← initialStx.mapM initialValue
  let sorted := (initial.zip valueTerms).qsort (fun x y ↦ x.1.1 < y.1.1)
  let k₀ := (sorted[0]?.map (·.1.1)).getD 0
  unless initial.isEmpty ||
      (sorted.size = order && sorted.zipIdx.all fun ((p, _), i) ↦ p.1 == k₀ + i) do
    if order = 1 then throwErrorAt ref "rsolve: give one initial value {seq} k = v"
    throwErrorAt ref "rsolve: give the {order} initial values {seq} k, …, {seq} (k + {order - 1}) \
      at consecutive indices"
  let aI := mkIdent seq
  let nI := mkIdent index
  let (type, proof) ← liftTermElabM do
    if initial.isEmpty then generalTheorem rec_ part roots aI nI ⟨equation⟩
    else ivpTheorem rec_ part roots aI nI ⟨equation⟩ k₀ (sorted.map (·.1.2)) (sorted.map (·.2))
  let answer ← liftTermElabM do
    lambdaLetTelescope type fun _ body ↦ do
      let some rhs ← ExpPolynomials.solutionRhs (lastConjunct body) | pure "see the statement"
      pure s!"{seq} {index} = {rhs}"
  logReport ref {
    domain := s!"{seq} : ℕ → ℝ"
    input := surfaceText equation ++ String.join
      (sorted.toList.map fun ((j, v), _) ↦ s!", {seq} {j} = {ratText v}")
    inputType := if initial.isEmpty then "recurrence" else "recurrence with initial values"
    output := answer
    outputType := if initial.isEmpty then "general solution"
      else "the sequence with these initial values"
  } #[← liftTermElabM <| checkedEvidence "rsolve"
      (if initial.isEmpty then "Closed form of every solution"
        else "A sequence has the recurrence and the initial values exactly when it is the \
          closed form")
      type proof]

end CAS.Command.RSolve

namespace CAS.Command

open Lean Elab Command

/-- `#cas [rsolve a n] eq` solves the linear recurrence `eq` with constant rational coefficients for
the sequence `a`, and `#cas [rsolve a n, a 0 = v₀, …] eq` gives the solution with those initial
values.

## Theorem
Without initial values the report proves
`∀ a : ℕ → ℝ, (∀ n, eq) ↔ ∃ c₁ … c_d, ∀ n, a n = y n` for the general solution `y` of a
recurrence of order `d` (`CAS.LinearRecurrence.rec_general`). With them it proves
`∀ a : ℕ → ℝ, (∀ n, eq) ∧ initial values ↔ ∀ n, a n = Y n` (`CAS.LinearRecurrence.rec_ivp`).

## Conditions and limits
The recurrence is linear in `a` with constant rational coefficients. The right side may contain
terms `c * n ^ j * r ^ n`, whose particular solution is found by undetermined coefficients. The
characteristic polynomial is split into rational roots, the roots of quadratic factors, the
factors that Hex finds when `CASHex.Factor` is imported, and kernel-checked enclosures
`AlgRoot.real` and `AlgRoot.complex` of the other roots. A recurrence of order `d` takes `d`
initial values at consecutive indices.

## Options
None.

## Examples
```lean
#cas [rsolve a n, a 0 = 1] (a (n + 1) = 2 * a n + 1)
```
```output
Output (the sequence with these initial values): a n = -1 + 2*2^n
```
```lean
#cas [rsolve a n] (a (n + 2) = 5 * a (n + 1) - 6 * a n)
```
```output
Output (general solution): a n = c₁*2^n + c₂*3^n
```

## In a proof
```lean
theorem rsolve_closed_form (a : ℕ → ℝ) (h : ∀ n, a (n + 1) = 2 * a n + 1) (h₀ : a 0 = 1) :
    ∀ n, a n = -1 + 2 * 2 ^ n := by
  intro n
  induction n with
  | zero =>
    rw [h₀]
    norm_num
  | succ n ih =>
    rw [h, ih]
    ring
```
The tactic `cas` does not prove the statements of `rsolve`, so the closed form is proved by
induction from the recurrence.

## See also
Mathematica `RSolve`, SymPy `rsolve`. Hex `Hex.ZPoly.factorize` (through `CASHex.Factor`)
splits the characteristic polynomial. The modes `sum`, `dsolve` and `roots`.

## Possible issues
```lean
#cas [rsolve a n] (a (n + 1) = a n + sin n)
```
```output
rsolve: the terms in n must be sums of c n^j r^n
```
The right side may contain polynomial and exponential terms in `n` only.
```lean
#cas [rsolve a n] (b (n + 1) = 2 * b n)
```
```output
rsolve: the equation is about the sequence b, but the mode names a; write #cas [rsolve b n]
```
The first identifier of the mode is the sequence that the recurrence determines.
```lean
#cas [rsolve a n, a 0 = 1] (a (n + 2) = 5 * a (n + 1) - 6 * a n)
```
```output
rsolve: give the 2 initial values a k, …, a (k + 1) at consecutive indices
```
Give two initial values at consecutive indices, such as `a 0 = 1, a 1 = 2`.
-/
syntax (name := casRSolveCommand)
  "#cas" "[" &"rsolve" ident ident (", " term)* "]" term : command

elab_rules : command
  | `(#cas [rsolve $a:ident $n:ident $[, $initial]*] $e:term) => do
      RSolve.logRSolve e a n (initial.map (·.raw)) e

end CAS.Command
