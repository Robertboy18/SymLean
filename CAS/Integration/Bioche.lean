/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Integration.Elementary
public import CAS.ClosedForm.Expression.Rational
public import CAS.ClosedForm.Pipeline.Configured

/-!
# Bioche's rules and trigonometric polynomials

An integrand with a single trigonometric phase `u` is a rational function `R(S, C)` of the atoms
`S = sin u` and `C = cos u`, with coefficients free of the integration coordinate. `abstracted?`
writes that function as a quotient of two polynomials in `S`, `C` and the remaining factors, from
which two kinds of candidates for the planner are built.

Bioche's rules choose a substitution from the symmetries of `R(S, C) du`:

* `t = cos u` when the form is invariant under `u ↦ -u`, that is `R(-S, C) = -R(S, C)`;
* `t = sin u` when it is invariant under `u ↦ π - u`, that is `R(S, -C) = -R(S, C)`;
* `t = tan u` when it is invariant under `u ↦ π + u`, that is `R(-S, -C) = R(S, C)`.

Each rule yields a rational integrand in `t`, which the planner integrates by its own search; the
primitive is then written back in `u` and divided by the slope of `u`. The tangent half-angle
substitution, which applies to every `R(S, C)`, stays the planner's fallback.

A polynomial in `S` and `C` over a denominator free of both is integrated directly by
`trigPolynomialCandidate?`: a monomial with an odd power is integrated by `t = cos u` or
`t = sin u`, and a monomial with even powers is reduced by `S² = 1 - C²` and the reduction
formula of `C^(2m)`.

## Implementation notes

The three rules are the classical rules of Bioche.
We decide each symmetry exactly on the normalized numerator `N` and denominator `D`:
`antiInvariant` tests `σN · D + N · σD = 0` and `invariant` tests `σN · D - N · σD = 0`, and a
flip is used only when no opaque factor, such as `sqrt S`, contains a flipped atom. `evenize`
rewrites the quotient over a denominator that the symmetry leaves unchanged, so that
`substitutions` can send every monomial to a polynomial in `t` through `S² = 1 - t²`,
`C² = 1 - t²` or `S^x C^y = t^x (1 + t²)^(-(x+y)/2)`, and `restore` writes a primitive back in
`u`, replacing `atan t` by `u` for `t = tan u`. The direct primitives use the binomial expansion
of `(1 - t²)^k t^b` (`oddPart`) and the recurrence for the primitive of `C^(2m)`
(`cosEvenPower`).

None of these identities is proved here. `IntegrationPlanner.biocheCandidate?` checks each
substitution candidate by differentiation during the search, while the planner passes the
primitive of a trigonometric polynomial on unchecked. In both cases `integrate?` accepts a result
only through `IntegrationCheck.certifyCandidate?`, when `IntegrationCheck.route` reduces the
derivative residual to literal zero, and branch conditions such as `cos u ≠ 0` for `t = tan u`
become requirements of the certificate.
-/

@[expose] public section

namespace CAS.IntegrationPlanner.Bioche

open CAS.Verified.Expr.Alg (Poly Monomial polyOf normalizePoly mulPoly addPoly subPoly
  polyExpr monoExpr)

/-- The index of the atom `S = sin u`, appended after the `n` coordinates. -/
def sinIndex (n : Nat) : Fin (n + 2) := (Fin.last n).castSucc

/-- The index of the atom `C = cos u`, the last index. -/
def cosIndex (n : Nat) : Fin (n + 2) := Fin.last (n + 1)

/-- The atom `S = sin u`. -/
def sinAtom (n : Nat) : Verified.Expr (Fin (n + 2)) := .var (sinIndex n)

/-- The atom `C = cos u`. -/
def cosAtom (n : Nat) : Verified.Expr (Fin (n + 2)) := .var (cosIndex n)

/-- An expression in the `n` coordinates, read in the coordinates and the two atoms. -/
def liftVars {n : Nat} : Verified.Expr (Fin n) → Verified.Expr (Fin (n + 2)) :=
  Verified.Expr.mapVars fun j ↦ .var j.castSucc.castSucc

/-- `R(S, C)`: `expr` with `sin phase` and `cos phase` replaced by the atoms, or `none` when the
integration coordinate survives the replacement, so that `expr` is not a function of `sin phase`
and `cos phase` alone. -/
def abstractTrig? {n : Nat} (i : Fin n) (phase expr : Verified.Expr (Fin n)) :
    Option (Verified.Expr (Fin (n + 2))) := do
  let lifted := liftVars phase
  let abstracted := Verified.Expr.abstractSubterm (.cos lifted) (cosIndex n)
    (Verified.Expr.abstractSubterm (.sin lifted) (sinIndex n) (liftVars expr))
  guard (Verified.Expr.containsVar i.castSucc.castSucc abstracted = false)
  return abstracted

/-- Whether a factor contains neither atom. -/
def trigFree {n : Nat} (factor : Verified.Expr (Fin (n + 2))) : Bool :=
  !Verified.Expr.containsVar (sinIndex n) factor && !Verified.Expr.containsVar (cosIndex n) factor

/-- The power of `S` in a monomial. -/
def sinCount {n : Nat} (m : Monomial (Fin (n + 2))) : Nat := m.count (sinAtom n)

/-- The power of `C` in a monomial. -/
def cosCount {n : Nat} (m : Monomial (Fin (n + 2))) : Nat := m.count (cosAtom n)

/-- The factors of a monomial other than the atoms themselves. -/
def otherFactors {n : Nat} (m : Monomial (Fin (n + 2))) : Monomial (Fin (n + 2)) :=
  m.filter fun f ↦ f != sinAtom n && f != cosAtom n

/-- Which opaque factors occur, an opaque factor being one that is neither an atom nor free of
both atoms (such as `sqrt S` or `exp (S C)`): those containing only `S`, only `C`, or both. -/
structure OpaqueFactors where
  /-- Some opaque factor contains `S` and not `C`. -/
  sinOnly : Bool
  /-- Some opaque factor contains `C` and not `S`. -/
  cosOnly : Bool
  /-- Some opaque factor contains both atoms. -/
  mixed : Bool

/-- Whether there is no opaque factor at all. -/
def OpaqueFactors.isEmpty (o : OpaqueFactors) : Bool := !o.sinOnly && !o.cosOnly && !o.mixed

/-- The opaque factors of the monomials of a polynomial. -/
def opaqueFactors {n : Nat} (p : Poly (Fin (n + 2))) : OpaqueFactors :=
  p.foldl (fun acc term ↦ term.2.foldl (fun acc f ↦
    if f == sinAtom n || f == cosAtom n then acc
    else
      let s := Verified.Expr.containsVar (sinIndex n) f
      let c := Verified.Expr.containsVar (cosIndex n) f
      { sinOnly := acc.sinOnly || (s && !c), cosOnly := acc.cosOnly || (c && !s)
        mixed := acc.mixed || (s && c) }) acc) ⟨false, false, false⟩

/-- The three symmetries of Bioche's test: `S ↦ -S` (from `u ↦ -u`), `C ↦ -C` (from
`u ↦ π - u`) and `(S, C) ↦ (-S, -C)` (from `u ↦ π + u`). -/
inductive Flip
  /-- `S ↦ -S`. -/
  | sin
  /-- `C ↦ -C`. -/
  | cos
  /-- `(S, C) ↦ (-S, -C)`. -/
  | both
deriving DecidableEq, Repr

/-- Whether the symmetry changes the sign of a monomial. -/
def Flip.odd {n : Nat} : Flip → Monomial (Fin (n + 2)) → Bool
  | .sin, m => sinCount m % 2 = 1
  | .cos, m => cosCount m % 2 = 1
  | .both, m => (sinCount m + cosCount m) % 2 = 1

/-- The image of a polynomial under the symmetry. Opaque factors are left alone, so the callers
apply a symmetry only when no opaque factor contains a flipped atom. -/
def Flip.apply {n : Nat} (σ : Flip) (p : Poly (Fin (n + 2))) : Poly (Fin (n + 2)) :=
  p.map fun term ↦ (if σ.odd term.2 then -term.1 else term.1, term.2)

/-- Whether `σ R = -R` for `R = N / D`, decided as `σN · D + N · σD = 0` on normalized
polynomials. -/
def antiInvariant {n : Nat} (σ : Flip) (N D : Poly (Fin (n + 2))) : Bool :=
  (addPoly (mulPoly (σ.apply N) D) (mulPoly N (σ.apply D))).isEmpty

/-- Whether `σ R = R` for `R = N / D`, decided as `σN · D - N · σD = 0`. -/
def invariant {n : Nat} (σ : Flip) (N D : Poly (Fin (n + 2))) : Bool :=
  (subPoly (mulPoly (σ.apply N) D) (mulPoly N (σ.apply D))).isEmpty

/-- The quotient `N / D` rewritten with a denominator that the symmetry leaves unchanged: `D` as
it is when every monomial is even, `N S / D S` (or with `C`) when every monomial is odd, and
`N σD / D σD` otherwise. -/
def evenize {n : Nat} (σ : Flip) (N D : Poly (Fin (n + 2))) :
    Poly (Fin (n + 2)) × Poly (Fin (n + 2)) :=
  if D.all fun term ↦ !σ.odd term.2 then (N, D)
  else if D.all fun term ↦ σ.odd term.2 then
    let atom : Poly (Fin (n + 2)) := [(1, [if σ = .sin then sinAtom n else cosAtom n])]
    (mulPoly N atom, mulPoly D atom)
  else
    (mulPoly N (σ.apply D), mulPoly D (σ.apply D))

/-- A monomial of other factors read back in the `n` coordinates. The coordinates stay, and an
atom inside a factor the rule allows becomes `t`, which is the integration coordinate `i`. -/
def lowerFactors {n : Nat} (i : Fin n) (m : Monomial (Fin (n + 2))) : Verified.Expr (Fin n) :=
  (monoExpr m).mapVars fun j ↦ if h : j.val < n then .var ⟨j.val, h⟩ else .var i

/-- A polynomial in the atoms read back in `t`: the monomial `q · m · S^x C^y` becomes
`q · m · image x y`. -/
def substitutePoly {n : Nat} (i : Fin n) (image : Nat → Nat → Verified.Expr (Fin n))
    (p : Poly (Fin (n + 2))) : Verified.Expr (Fin n) :=
  Verified.Expr.mkAddList (p.map fun term ↦
    Verified.Expr.mkMul (Verified.Expr.mkRatConst term.1)
      (Verified.Expr.mkMul (lowerFactors i (otherFactors term.2))
        (image (sinCount term.2) (cosCount term.2))))

/-- A substituted integrand in `t`, written in the integration coordinate, with the images that
write its primitive back in `u`. -/
structure Substitution (n : Nat) where
  /-- The integrand in `t`, per unit slope of `u`. -/
  body : Verified.Expr (Fin n)
  /-- The expression of `t` in `u`. -/
  tImage : Verified.Expr (Fin n)
  /-- The phase `u`, which replaces `atan t` in the primitive for the rule `t = tan u`. -/
  atanImage? : Option (Verified.Expr (Fin n))

/-- An integrand with one trigonometric phase, as a quotient of polynomials in the atoms. -/
structure Abstracted (n : Nat) where
  /-- The phase `u`. -/
  phase : Verified.Expr (Fin n)
  /-- The derivative of `u` in the integration coordinate, nonzero and free of it. -/
  slope : Verified.Expr (Fin n)
  /-- The numerator of `R(S, C)`. -/
  numerator : Poly (Fin (n + 2))
  /-- The denominator of `R(S, C)`. -/
  denominator : Poly (Fin (n + 2))
  /-- The opaque factors of both sides. -/
  shape : OpaqueFactors

/-- The abstraction of an integrand whose list of trigonometric phases has exactly one entry `u`,
of nonzero slope free of the integration coordinate. -/
def abstracted? {n : Nat} (i : Fin n) (phases : List (Verified.Expr (Fin n)))
    (expr : Verified.Expr (Fin n)) : Option (Abstracted n) := do
  let [phase] := phases | none
  let slope ← Elementary.nonzeroIndependentDerivative? i phase
  let body ← abstractTrig? i phase expr
  let fraction := Verified.Expr.Alg.fractionResult body
  let numerator := polyOf fraction.num
  let denominator := polyOf fraction.den
  let shapeNumerator := opaqueFactors numerator
  let shapeDenominator := opaqueFactors denominator
  return { phase, slope, numerator, denominator,
           shape := ⟨shapeNumerator.sinOnly || shapeDenominator.sinOnly,
             shapeNumerator.cosOnly || shapeDenominator.cosOnly,
             shapeNumerator.mixed || shapeDenominator.mixed⟩ }

/-- Bioche's rules that apply, in the order `t = cos u` (when `σ_sin R = -R` and no opaque factor
contains `S`), `t = sin u` (when `σ_cos R = -R` and no opaque factor contains `C`) and `t = tan u`
(when `σ_both R = R` and there is no opaque factor).

For the rule `t = tan u` the monomial `S^x C^y` (with `x + y` even) is `t^x (1 + t²)^(-(x+y)/2)`.
With `k` the largest half degree of a side, that side is `(1 + t²)^(-k)` times a polynomial in
`t`, and `du = dt / (1 + t²)` leaves a power of `1 + t²` on one side of the quotient. -/
def substitutions {n : Nat} (i : Fin n) (a : Abstracted n) : List (Substitution n) :=
  let t : Verified.Expr (Fin n) := .var i
  let oneMinus : Verified.Expr (Fin n) := 1 - t ^ 2
  let onePlus : Verified.Expr (Fin n) := 1 + t ^ 2
  let cosRule : List (Substitution n) :=
    if !a.shape.sinOnly && !a.shape.mixed && antiInvariant .sin a.numerator a.denominator then
      let (N, D) := evenize .sin a.numerator a.denominator
      let image := fun x y ↦ Verified.Expr.mkMul (Verified.Expr.mkPow oneMinus (x / 2))
        (Verified.Expr.mkPow t y)
      [{ body := .neg (.div (substitutePoly i image N) (substitutePoly i image D))
         tImage := .cos a.phase, atanImage? := none }]
    else []
  let sinRule : List (Substitution n) :=
    if !a.shape.cosOnly && !a.shape.mixed && antiInvariant .cos a.numerator a.denominator then
      let (N, D) := evenize .cos a.numerator a.denominator
      let image := fun x y ↦ Verified.Expr.mkMul (Verified.Expr.mkPow t x)
        (Verified.Expr.mkPow oneMinus (y / 2))
      [{ body := .div (substitutePoly i image N) (substitutePoly i image D)
         tImage := .sin a.phase, atanImage? := none }]
    else []
  let tanRule : List (Substitution n) :=
    if a.shape.isEmpty && invariant .both a.numerator a.denominator then
      let (N, D) := evenize .both a.numerator a.denominator
      let degree := fun (p : Poly (Fin (n + 2))) ↦
        p.foldl (fun acc term ↦ max acc ((sinCount term.2 + cosCount term.2) / 2)) 0
      let kN := degree N
      let kD := degree D
      let side := fun (k : Nat) (p : Poly (Fin (n + 2))) ↦ substitutePoly i (fun x y ↦
        Verified.Expr.mkMul (Verified.Expr.mkPow t x)
          (Verified.Expr.mkPow onePlus (k - (x + y) / 2))) p
      let body : Verified.Expr (Fin n) :=
        if kN + 1 ≤ kD then
          .div (Verified.Expr.mkMul (side kN N) (Verified.Expr.mkPow onePlus (kD - kN - 1)))
            (side kD D)
        else
          .div (side kN N)
            (Verified.Expr.mkMul (side kD D) (Verified.Expr.mkPow onePlus (kN + 1 - kD)))
      [{ body, tImage := .div (.sin a.phase) (.cos a.phase), atanImage? := some a.phase }]
    else []
  cosRule ++ sinRule ++ tanRule

/-- A primitive `F(t)` written back in `u`: `t` becomes `tImage`, and for the rule `t = tan u`
the subterm `atan t` becomes `u`. -/
def restore {n : Nat} (i : Fin n) (primitive tImage : Verified.Expr (Fin n))
    (atanImage? : Option (Verified.Expr (Fin n))) : Verified.Expr (Fin n) :=
  let lifted : Verified.Expr (Fin (n + 1)) := primitive.mapVars fun j ↦ .var j.castSucc
  let marked :=
    match atanImage? with
    | some _ => Verified.Expr.abstractSubterm (.atan (.var i.castSucc)) (Fin.last n) lifted
    | none => lifted
  marked.mapVars fun j ↦
    if h : j.val < n then
      if (⟨j.val, h⟩ : Fin n) = i then tImage else .var ⟨j.val, h⟩
    else atanImage?.getD (.var i)

/-- The value of an expression that is a rational constant. -/
def rationalValue? {n : Nat} (expr : Verified.Expr (Fin n)) : Option ℚ :=
  match polyOf expr with
  | [] => some 0
  | [(q, [])] => some q
  | _ => none

/-- `expr / slope`, written as a rational multiple when the slope is a rational constant. -/
def divideBySlope {n : Nat} (expr slope : Verified.Expr (Fin n)) : Verified.Expr (Fin n) :=
  match rationalValue? slope with
  | some q => if q = 1 then expr else Verified.Expr.mkMul (Verified.Expr.mkRatConst (1 / q)) expr
  | none => Verified.Expr.simplifyDiv expr slope

/-- The primitive of `C^(2m)` per unit slope by the reduction formula, as the coefficient `c` of
`x` and the terms `(cⱼ, 2j + 1)` of `cⱼ S C^(2j+1)`. -/
def cosEvenPower : Nat → ℚ × List (ℚ × Nat)
  | 0 => (1, [])
  | m + 1 =>
      let k : ℚ := 2 * (m + 1)
      let (x, sc) := cosEvenPower m
      let factor := (k - 1) / k
      (factor * x, (1 / k, 2 * m + 1) :: sc.map fun term ↦ (factor * term.1, term.2))

/-- The monomial `S^a`. -/
def sinPower {n : Nat} (a : Nat) : Monomial (Fin (n + 2)) := List.replicate a (sinAtom n)

/-- The monomial `C^b`. -/
def cosPower {n : Nat} (b : Nat) : Monomial (Fin (n + 2)) := List.replicate b (cosAtom n)

/-- The primitive of `(1 - t²)^k t^b` as the terms `(c, p)` of `c t^p`, from the binomial
expansion. -/
def oddPart (k b : Nat) : List (ℚ × Nat) :=
  (List.range (k + 1)).map fun j ↦
    let p := 2 * j + b + 1
    (((k.choose j : ℚ) * (-1) ^ j) / p, p)

/-- The primitive of `q · m · S^a C^b` per unit slope, as the coefficient of `x` and the
trigonometric part. An odd power is integrated by `t = cos u` or `t = sin u` (the smaller one
when both are odd), and two even powers by `S² = 1 - C²` and `cosEvenPower`. -/
def monomialPrimitive {n : Nat} (term : ℚ × Monomial (Fin (n + 2))) :
    Poly (Fin (n + 2)) × Poly (Fin (n + 2)) :=
  let q := term.1
  let r := otherFactors term.2
  let a := sinCount term.2
  let b := cosCount term.2
  if a % 2 = 1 && (b % 2 = 0 || a < b) then
    ([], (oddPart (a / 2) b).map fun term ↦ (-q * term.1, r ++ cosPower term.2))
  else if b % 2 = 1 then
    ([], (oddPart (b / 2) a).map fun term ↦ (q * term.1, r ++ sinPower term.2))
  else
    (List.range (a / 2 + 1)).foldl (fun (acc : Poly (Fin (n + 2)) × Poly (Fin (n + 2))) j ↦
      let coefficient := q * (((a / 2).choose j : ℚ) * (-1) ^ j)
      let (x, sc) := cosEvenPower (j + b / 2)
      (acc.1 ++ [(coefficient * x, r)],
       acc.2 ++ sc.map fun term ↦ (coefficient * term.1, r ++ sinPower 1 ++ cosPower term.2)))
      ([], [])

/-- The terms of a trigonometric part sorted by the power of `C`, then by the power of `S`. -/
def sortTerms {n : Nat} (p : Poly (Fin (n + 2))) : Poly (Fin (n + 2)) :=
  p.mergeSort fun s t ↦
    cosCount s.2 < cosCount t.2 || (cosCount s.2 == cosCount t.2 && sinCount s.2 ≤ sinCount t.2)

/-- The sum of the terms `q e`, written with a subtraction for each negative coefficient. -/
def signedSum {n : Nat} (terms : List (ℚ × Verified.Expr (Fin n))) : Verified.Expr (Fin n) :=
  (terms.foldl (fun (acc : Option (Verified.Expr (Fin n))) (term : ℚ × Verified.Expr (Fin n)) ↦
    let magnitude := Verified.Expr.mkMul (Verified.Expr.mkRatConst |term.1|) term.2
    match acc with
    | none => some (if term.1 < 0 then Verified.Expr.mkNeg magnitude else magnitude)
    | some s => some (if term.1 < 0 then .sub s magnitude else .add s magnitude)) none).getD 0

/-- The primitive of a polynomial in `sin u` and `cos u` over a denominator free of both, by
`monomialPrimitive` on each monomial and division by the slope of `u`. -/
def trigPolynomialCandidate? {n : Nat} (i : Fin n) (phases : List (Verified.Expr (Fin n)))
    (expr : Verified.Expr (Fin n)) : Option (Verified.Expr (Fin n)) := do
  let a ← abstracted? i phases expr
  guard a.shape.isEmpty
  guard (a.denominator.all fun term ↦ term.2.all trigFree)
  guard (a.numerator.any fun term ↦ !(term.2.all trigFree))
  let parts := a.numerator.map monomialPrimitive
  let xPart := normalizePoly (parts.flatMap (·.1))
  let trigPart := sortTerms (normalizePoly (parts.flatMap (·.2)))
  let x : Verified.Expr (Fin n) := .var i
  let slope? := rationalValue? a.slope
  let trigTerm := fun (term : ℚ × Monomial (Fin (n + 2))) ↦
    let body := Verified.Expr.mkMul (lowerFactors i (otherFactors term.2))
      (Verified.Expr.mkMul (Verified.Expr.mkPow (.sin a.phase) (sinCount term.2))
        (Verified.Expr.mkPow (.cos a.phase) (cosCount term.2)))
    match slope? with
    | some q => (term.1 / q, body)
    | none => (term.1, Verified.Expr.simplifyDiv body a.slope)
  let xTerms := xPart.map fun term ↦ (term.1, Verified.Expr.mkMul (lowerFactors i term.2) x)
  let primitive := signedSum (xTerms ++ trigPart.map trigTerm)
  let denominator : Verified.Expr (Fin n) := (polyExpr a.denominator).mapVars fun j ↦
    if h : j.val < n then .var ⟨j.val, h⟩ else .var i
  some (Verified.Expr.simplifyDiv primitive denominator)

end CAS.IntegrationPlanner.Bioche
