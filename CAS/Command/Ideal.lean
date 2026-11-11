/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/
module

public import CAS.Command.Common
public import CAS.Command.Groebner
public import CAS.Polynomial.Sparse.Groebner
public import CAS.Tactic.RouteRegistry
public import CAS.Tactic.Syntax
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.Tactic.Ring.Basic
public meta import CAS.Command.Common
public meta import CAS.Command.Groebner
public meta import CAS.Command.PolySystems
public meta import CAS.Command.Report
public meta import CAS.Command.Syntax
public meta import CAS.Tactic.RouteRegistry
public meta import CAS.Tactic.ProofCarrier
public meta import CAS.Tactic.Explanation
public meta import CAS.Tactic.KernelReadBack
public meta import Mathlib.Tactic.Ring.Basic

/-!
# Ideal certificates

We prove statements about polynomial ideals from certificates that a search proposes and the
kernel checks. `#cas [groebner x, y] [f₁, ..., fₘ]` computes the reduced Gröbner basis of the
inputs for the lexicographic order `x > y` with SymLean's Buchberger algorithm and prints it as
`g₁, ..., gₖ`, each element scaled to coprime integer coefficients with a positive leading
coefficient. It proves, in `MvPolynomial (Fin n) ℚ`, that the `gⱼ` span the ideal of the inputs
and that they are a Gröbner basis for `MonomialOrder.lex`: the leading term of every nonzero
element of the ideal is divisible by the leading term of one of them.
`#cas [member x, y] f [g₁, ..., gₘ]` proves `f ∈ Ideal.span {g₁, ..., gₘ}`. The bare `cas`
tactic proves equalities of spans and memberships in any commutative ring, and the Gröbner
property for `MonomialOrder.lex` of a set literal in `MvPolynomial (Fin n) ℚ`; it refuses the
property for another monomial order before any division.

## Main definitions

* `CAS.Command.Ideal.spanEquality`: the proof that the basis of a Buchberger run spans the ideal
  of its inputs.
* `CAS.Command.Ideal.groebnerProperty`: the proof of the Gröbner property of a basis.
* `CAS.Command.Ideal.idealRoute`: the route of `cas` for ideal goals.

## Implementation notes

The search, Buchberger's algorithm in `CAS/Command/Groebner.lean`, records how each polynomial
of the derivation arises from earlier ones. Each step becomes one identity
`(D + 1) * a = ∑ cᵢ tᵢ` between ring elements, where every `tᵢ` is already known to lie in the
ideal; `ring1` proves the identity and closure of the ideal under sums and multiples gives `a`.
A factor `D + 1` other than one is cancelled only in a ℚ-algebra.

For the Gröbner property we divide the S-polynomial of every pair of basis elements by the basis
in meta code and record the quotients. The kernel checks on sparse polynomials that each
S-polynomial is the combination of the basis with these quotients and that every term of a
quotient times the leading monomial of its divisor lies below the least common multiple of the
two leading monomials (`CAS.Polynomial.Sparse.groebnerCertified`); Buchberger's criterion
(`CAS.Polynomial.Buchberger.exists_leadingTerm_dvd_of_sPolynomial`) turns the certificate into the
property. The checker and `CAS.Polynomial.Sparse.isGroebner_of_groebnerCertified`, which applies
the criterion to it, are in `CAS/Polynomial/Sparse/Groebner.lean`; the criterion itself is
proved in `CAS/Polynomial/Buchberger.lean`. A nonzero remainder of `f` modulo the computed basis
is reported as a hint and never as a proof that `f` is not in the ideal.
-/

public section

namespace CAS.IdealCertificate

/-- If `a = b` and `b ∈ I` for an ideal `I` of a semiring, then `a ∈ I`; this is `h ▸ hb`. It is
kept because the ideal tactic builds it by name with `mkAppM`, which cannot elaborate `▸`. -/
theorem mem_of_eq {R : Type*} [Semiring R] {I : Ideal R} {a b : R} (h : a = b) (hb : b ∈ I) :
    a ∈ I := h ▸ hb

/-- In a commutative ring that is a `ℚ`-algebra, if `(D + 1) a ∈ I` for a natural `D`, then
`a ∈ I`. -/
theorem mem_of_succ_mul_mem {R : Type*} [CommRing R] [Algebra ℚ R] {I : Ideal R} {a : R}
    (D : ℕ) (h : ((D + 1 : ℕ) : R) * a ∈ I) : a ∈ I := by
  have hu : IsUnit ((D + 1 : ℕ) : R) := by
    rw [← map_natCast (algebraMap ℚ R)]
    exact (IsUnit.mk0 ((D + 1 : ℕ) : ℚ) (by exact_mod_cast Nat.succ_ne_zero D)).map _
  exact (Ideal.unit_mul_mem_iff_mem I hu).mp h

/-- A member `a ∈ s` of a set in a semiring lies in `Ideal.span s`; this is `Ideal.subset_span h`.
It is kept because the ideal tactic builds it by name from `h` with `mkAppOptM` and `mkAppM`, which
need an explicit membership argument; `Ideal.subset_span` has none. -/
theorem mem_span_of_mem {R : Type*} [Semiring R] {s : Set R} {a : R} (h : a ∈ s) :
    a ∈ Ideal.span s := Ideal.subset_span h

/-- If `a ∈ J` and `s ⊆ J` for an ideal `J` of a semiring, then `insert a s ⊆ J`; this is
`Set.insert_subset`. It is kept because the ideal tactic builds it by name with `mkAppM` from proofs
of `a ∈ J`, and `mkAppM` would have to infer the set `(J : Set R)` of `Set.insert_subset` from such
a proof. -/
theorem insert_subset_of_mem {R : Type*} [Semiring R] {J : Ideal R} {a : R} {s : Set R}
    (ha : a ∈ J) (hs : s ⊆ J) : insert a s ⊆ (J : Set R) := Set.insert_subset ha hs

/-- If `a ∈ J` for an ideal `J` of a semiring, then `{a} ⊆ J`; this is
`Set.singleton_subset_iff.mpr`. It is kept because the ideal tactic builds it by name with `mkAppM`,
which cannot form `.mpr` of an iff. -/
theorem singleton_subset_of_mem {R : Type*} [Semiring R] {J : Ideal R} {a : R} (ha : a ∈ J) :
    ({a} : Set R) ⊆ J := Set.singleton_subset_iff.mpr ha

/-- If `s ⊆ J` for an ideal `J` of a semiring, then `Ideal.span s ≤ J`; this is `Ideal.span_le.mpr`.
It is kept because the ideal tactic builds it by name with `mkAppM`, which cannot form `.mpr` of an
iff. -/
theorem span_le_of_subset {R : Type*} [Semiring R] {s : Set R} {J : Ideal R} (h : s ⊆ J) :
    Ideal.span s ≤ J := Ideal.span_le.mpr h

end CAS.IdealCertificate

end

public meta section

namespace CAS.Command.Ideal

open Lean Elab Command Meta Term
open CAS.Command.InfoView
open CAS.Command.Groebner

/-- Whether `type` is a division ring, so that `a / k` for a numeral `k ≠ 0` is `a * k⁻¹`. -/
def isDivisionRing (type : Lean.Expr) : MetaM Bool := do
  try
    let u ← getDecLevel type
    return (← synthInstance? (mkApp (mkConst ``DivisionRing [u]) type)).isSome
  catch _ =>
    return false

/-- The value of a natural number literal. -/
def natLiteral? (e : Lean.Expr) : MetaM (Option Nat) := do
  let e ← instantiateMVars e
  if let some n := e.rawNatLit? then return some n
  if e.isAppOfArity ``OfNat.ofNat 3 then
    return (e.getArg! 1).rawNatLit?
  return none

/-- The polynomial structure of a ring element over atoms: sums, differences, products,
negations, powers with literal exponents, numerals, and division by a nonzero numeral in a
division ring. Every other subterm is an atom; atoms equal up to reducible unfolding share an
index. -/
partial def reifyPoly (e : Lean.Expr) : StateT (Array Lean.Expr) MetaM (Verified.Expr ℕ) := do
  let e ← instantiateMVars e
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => return .add (← reifyPoly a) (← reifyPoly b)
  | (``HSub.hSub, #[_, _, _, _, a, b]) => return .sub (← reifyPoly a) (← reifyPoly b)
  | (``HMul.hMul, #[_, _, _, _, a, b]) => return .mul (← reifyPoly a) (← reifyPoly b)
  | (``Neg.neg, #[_, _, a]) => return .neg (← reifyPoly a)
  | (``HPow.hPow, #[_, exponentType, _, _, a, k]) =>
      if exponentType.isConstOf ``Nat then
        if let some k ← natLiteral? k then
          if k ≤ 1000 then return .pow (← reifyPoly a) k
      atom e
  | (``HDiv.hDiv, #[type, _, _, _, a, b]) =>
      let divisionRing ← isDivisionRing type
      if let some k ← natLiteral? b then
        if k ≠ 0 && divisionRing then return .div (← reifyPoly a) (.nat k)
      atom e
  | (``OfNat.ofNat, #[_, n, _]) =>
      if let some n := n.rawNatLit? then return .nat n
      atom e
  | _ => atom e
where
  atom (e : Lean.Expr) : StateT (Array Lean.Expr) MetaM (Verified.Expr ℕ) := do
    let atoms ← get
    for h : i in [0:atoms.size] do
      if ← withReducible (isDefEq atoms[i] e) then return .var i
    set (atoms.push e)
    return .var atoms.size

/-- A reified polynomial over the first `n` atoms. -/
def overAtoms (n : Nat) (p : Verified.Expr ℕ) : Verified.Expr (Fin n) :=
  p.mapVars fun i ↦ if h : i < n then .var ⟨i, h⟩ else .nat 0

/-- The elements of a set literal `{a₁, ..., aₙ}`, each with a proof that it belongs to the
set. The set must be written with `insert` and a singleton, as `{a, b}` elaborates, and is read
without unfolding: a `Finset` coercion, a set behind a definition and the empty set give `none`. -/
partial def setMembers? (s : Lean.Expr) : MetaM (Option (Array (Lean.Expr × Lean.Expr))) := do
  let s ← instantiateMVars s
  match s.getAppFnArgs with
  | (``Insert.insert, #[_, _, _, x, rest]) =>
      let some members ← setMembers? rest | return none
      let mut result := #[(x, ← mkAppM ``Set.mem_insert #[x, rest])]
      for (y, h) in members do
        result := result.push (y, ← mkAppM ``Set.mem_insert_of_mem #[x, h])
      return some result
  | (``Singleton.singleton, #[_, _, _, x]) =>
      return some #[(x, ← mkAppM ``Set.mem_singleton #[x])]
  | _ => return none

/-- The product of two polynomials. -/
def mulPoly (p q : Groebner.Poly) : Groebner.Poly :=
  p.foldl (fun t (m, c) ↦ Groebner.add t (Groebner.mulTerm m c q)) []

/-- The `k`-th power of a polynomial in `n` variables. -/
def powPoly (n : Nat) (p : Groebner.Poly) (k : Nat) : Groebner.Poly := Id.run do
  let mut result := Groebner.constant n 1
  for _ in [0:k] do
    result := mulPoly result p
  return result

/-- The value of a constant polynomial. -/
def constantOf? : Groebner.Poly → Option ℚ
  | [] => some 0
  | [(m, c)] => if Groebner.degree m == 0 then some c else none
  | _ => none

/-- The polynomial of an expression built from rational numbers and variables by sums,
differences, products, negations, powers and division by nonzero constants. -/
def poly? {n : Nat} : Verified.Expr (Fin n) → Option Groebner.Poly
  | .nat k => some (Groebner.constant n (k : ℚ))
  | .int k => some (Groebner.constant n (k : ℚ))
  | .rat num den => some (Groebner.constant n (Rat.divInt num (den : ℤ)))
  | .var i => some (Groebner.var n i.val)
  | .add a b => do
      let pa ← poly? a
      let pb ← poly? b
      some (Groebner.add pa pb)
  | .sub a b => do
      let pa ← poly? a
      let pb ← poly? b
      some (Groebner.add pa (Groebner.scale (-1) pb))
  | .mul a b => do
      let pa ← poly? a
      let pb ← poly? b
      some (mulPoly pa pb)
  | .neg a => do
      let pa ← poly? a
      some (Groebner.scale (-1) pa)
  | .pow a k => do
      let pa ← poly? a
      some (powPoly n pa k)
  | .div a b => do
      let pa ← poly? a
      let pb ← poly? b
      let c ← constantOf? pb
      if c == 0 then none else some (Groebner.scale (1 / c) pa)
  | _ => none

/-- Whether a polynomial is the constant one. -/
def isOne (p : Groebner.Poly) : Bool := constantOf? p == some 1

/-- The least common multiple of the denominators of the coefficients. -/
def denLcm (ps : List Groebner.Poly) : Nat :=
  ps.foldl (fun acc p ↦ p.foldl (fun (acc : Nat) (_, c) ↦ Nat.lcm acc c.den) acc) 1

/-- The positive rational `s` such that `s * p` has coprime integer coefficients. -/
def primitiveScale (p : Groebner.Poly) : ℚ :=
  let l := denLcm [p]
  let g := p.foldl (fun (acc : Nat) (_, c) ↦ Nat.gcd acc (c * (l : ℚ)).num.natAbs) 0
  if g == 0 then 1 else (l : ℚ) / g

/-- The primitive scale, with the sign that makes the leading coefficient positive. -/
def normalScale (p : Groebner.Poly) : ℚ :=
  if (Groebner.lead p).2 < 0 then -primitiveScale p else primitiveScale p

/-- `a ^ k` for a natural number `k`. -/
def mkPowNat (a : Lean.Expr) (k : Nat) : MetaM Lean.Expr := do
  let type ← inferType a
  let u ← getDecLevel type
  let inst ← synthInstance (mkApp3 (mkConst ``HPow [u, 0, u]) type (mkConst ``Nat) type)
  return mkApp6 (mkConst ``HPow.hPow [u, 0, u]) type (mkConst ``Nat) type inst a (mkNatLit k)

/-- `-a`. -/
def mkNegation (a : Lean.Expr) : MetaM Lean.Expr := do
  let type ← inferType a
  let u ← getDecLevel type
  let inst ← synthInstance (mkApp (mkConst ``Neg [u]) type)
  return mkApp3 (mkConst ``Neg.neg [u]) type inst a

/-- Whether `ring` is a ℚ-algebra. -/
def isRationalAlgebra (ring : Lean.Expr) : MetaM Bool := do
  try
    let algebra ← mkAppOptM ``Algebra #[some (mkConst ``Rat), some ring, none, none]
    return (← synthInstance? algebra).isSome
  catch _ =>
    return false

/-- A commutative ring with the terms that stand for the variables of the polynomials. -/
structure Ctx where
  /-- The ring. -/
  ring : Lean.Expr
  /-- The variables, in the order of the exponents of a monomial. -/
  vars : Array Lean.Expr
  /-- `fun a b : ℚ ↦ C (a / b)`, when the ring has rational constants. -/
  ratC? : Option Lean.Expr := none
  /-- Whether the ring is a ℚ-algebra, so that a factor `D + 1` can be cancelled. -/
  rationalAlgebra : Bool

/-- The context of a commutative ring given by the user, with atoms as variables. -/
def Ctx.ofRing (ring : Lean.Expr) (vars : Array Lean.Expr) : MetaM Ctx := do
  let u ← getDecLevel ring
  if (← synthInstance? (mkApp (mkConst ``CommRing [u]) ring)).isNone then
    throwError "{ring} is not a commutative ring"
  return { ring, vars, rationalAlgebra := ← isRationalAlgebra ring }

/-- Elaborate a closed term. -/
def elabClosed (stx : Term) : TermElabM Lean.Expr := do
  let e ← elabTerm stx none
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

/-- The context `MvPolynomial (Fin n) ℚ` with the variables `X 0, ..., X (n - 1)`. -/
def Ctx.mvPolynomial (n : Nat) : TermElabM Ctx := do
  let nT : Term := ⟨Syntax.mkNumLit (toString n)⟩
  let ring ← elabClosed (← `(MvPolynomial (Fin $nT) ℚ))
  let vars ← (Array.range n).mapM fun i ↦ do
    let iT : Term := ⟨Syntax.mkNumLit (toString i)⟩
    elabClosed (← `((MvPolynomial.X ($iT : Fin $nT) : MvPolynomial (Fin $nT) ℚ)))
  let ratC ← elabClosed (← `(fun a b : ℚ ↦ (MvPolynomial.C (a / b) : MvPolynomial (Fin $nT) ℚ)))
  return { ring, vars, ratC? := some ratC, rationalAlgebra := true }

/-- The term for a nonnegative rational coefficient. -/
def coefficientExpr (ctx : Ctx) (c : ℚ) : MetaM Lean.Expr := do
  if c.den == 1 then
    mkNumeral ctx.ring c.num.toNat
  else
    let some ratC := ctx.ratC? |
      throwError "internal error: the coefficient {c} needs rational constants in {ctx.ring}"
    let num ← mkNumeral (mkConst ``Rat) c.num.toNat
    let den ← mkNumeral (mkConst ``Rat) c.den
    return ratC.beta #[num, den]

/-- The term `c * x₁ ^ e₁ * ... * xₙ ^ eₙ` for a nonnegative coefficient `c`, without a factor
one. -/
def termExpr (ctx : Ctx) (m : Groebner.Mono) (c : ℚ) : MetaM Lean.Expr := do
  let mut result? : Option Lean.Expr := none
  if c != 1 then
    let coefficient ← coefficientExpr ctx c
    result? := some coefficient
  for i in [0:ctx.vars.size] do
    let e := m.getD i 0
    if e == 0 then continue
    let x := ctx.vars[i]!
    let factor ← if e == 1 then pure x else mkPowNat x e
    let next ← match result? with
      | none => pure factor
      | some r => mkMul r factor
    result? := some next
  match result? with
  | some r => return r
  | none => coefficientExpr ctx c

/-- The term for a polynomial: its terms in decreasing lexicographic order, a negative first term
as a negation, later negative terms as subtractions, and `0` for the zero polynomial. -/
def polyExpr (ctx : Ctx) (p : Groebner.Poly) : MetaM Lean.Expr := do
  let mut result? : Option Lean.Expr := none
  for (m, c) in p do
    let t ← termExpr ctx m (if c < 0 then -c else c)
    let next ← match result? with
      | none => if c < 0 then mkNegation t else pure t
      | some r => if c < 0 then mkSub r t else mkAdd r t
    result? := some next
  match result? with
  | some r => return r
  | none => mkNumeral ctx.ring 0

/-- The term for a rational number and whether it is an integer. -/
def rationalExpr (ctx : Ctx) (q : ℚ) : MetaM (Lean.Expr × Bool) := do
  let magnitude ← coefficientExpr ctx (if q < 0 then -q else q)
  let term ← if q < 0 then mkNegation magnitude else pure magnitude
  return (term, q.den == 1)

/-- The term for an expression in the variables of the context, and whether all its numbers are
integers. Division is allowed by nonzero constants only. -/
partial def typedExpr {n : Nat} (ctx : Ctx) : Verified.Expr (Fin n) → MetaM (Lean.Expr × Bool)
  | .nat k => do
      let term ← mkNumeral ctx.ring k
      return (term, true)
  | .int k => do
      let magnitude ← mkNumeral ctx.ring k.natAbs
      let term ← if k < 0 then mkNegation magnitude else pure magnitude
      return (term, true)
  | .rat num den => rationalExpr ctx (Rat.divInt num (den : ℤ))
  | .var i => return (ctx.vars[i.val]!, true)
  | .add a b => do
      let (x, xIntegral) ← typedExpr ctx a
      let (y, yIntegral) ← typedExpr ctx b
      let term ← mkAdd x y
      return (term, xIntegral && yIntegral)
  | .sub a b => do
      let (x, xIntegral) ← typedExpr ctx a
      let (y, yIntegral) ← typedExpr ctx b
      let term ← mkSub x y
      return (term, xIntegral && yIntegral)
  | .mul a b => do
      let (x, xIntegral) ← typedExpr ctx a
      let (y, yIntegral) ← typedExpr ctx b
      let term ← mkMul x y
      return (term, xIntegral && yIntegral)
  | .neg a => do
      let (x, integral) ← typedExpr ctx a
      let term ← mkNegation x
      return (term, integral)
  | .pow a k => do
      let (x, integral) ← typedExpr ctx a
      let term ← mkPowNat x k
      return (term, integral)
  | .div a b => do
      let some c := (poly? b).bind constantOf? |
        throwError "not a polynomial with rational coefficients: it divides by a nonconstant"
      if c == 0 then
        throwError "not a polynomial with rational coefficients: it divides by zero"
      if let some d := (poly? a).bind constantOf? then
        return ← rationalExpr ctx (d / c)
      let (x, integral) ← typedExpr ctx a
      if 1 / c == 1 then
        return (x, integral)
      let (r, rIntegral) ← rationalExpr ctx (1 / c)
      let term ← mkMul r x
      return (term, integral && rIntegral)
  | _ => throwError "not a polynomial with rational coefficients"

/-- The set literal `{a₁, ..., aₙ}` of elements of `ring` and proofs that each `aᵢ` belongs to
it. -/
def setLiteral (ring : Lean.Expr) (elements : Array Lean.Expr) :
    MetaM (Lean.Expr × Array Lean.Expr) := do
  let some last := elements.back? | throwError "internal error: an empty set"
  let setType ← mkAppM ``Set #[ring]
  let mut set ← mkAppOptM ``Singleton.singleton #[some ring, some setType, none, some last]
  let mut proofs : Array Lean.Expr := #[← mkAppM ``Set.mem_singleton #[last]]
  for a in elements.pop.reverse do
    let previous := set
    set ← mkAppM ``Insert.insert #[a, previous]
    let mut lifted : Array Lean.Expr := #[← mkAppM ``Set.mem_insert #[a, previous]]
    for h in proofs do
      lifted := lifted.push (← mkAppM ``Set.mem_insert_of_mem #[a, h])
    proofs := lifted
  return (set, proofs)

/-- The element `a` of a proof of `a ∈ I`. -/
def memberOf (h : Lean.Expr) : MetaM Lean.Expr := do
  return (← instantiateMVars (← inferType h)).appArg!

/-- A proof of `a ∈ I` from the identity `(D + 1) * a = ∑ cᵢ * tᵢ`, or `a = ∑ cᵢ * tᵢ` without
`D`, which `identity` proves. The summands are the coefficients (`none` for one) and proofs of
`tᵢ ∈ I`. -/
def combine (ctx : Ctx) (I a : Lean.Expr) (D? : Option Nat)
    (summands : Array (Option Lean.Expr × Lean.Expr)) (identity : MVarId → TermElabM Unit) :
    TermElabM Lean.Expr := do
  if D?.isSome && !ctx.rationalAlgebra then
    throwError "the certificate divides by {D?.getD 0 + 1}, and {ctx.ring} is not a ℚ-algebra"
  let mut sum? : Option Lean.Expr := none
  for (c?, h) in summands do
    let m ← match c? with
      | none => pure h
      | some c => mkAppM ``Ideal.mul_mem_left #[I, c, h]
    let next ← match sum? with
      | none => pure m
      | some s => mkAppM ``Ideal.add_mem #[I, s, m]
    sum? := some next
  let hsum ← match sum? with
    | some s => pure s
    | none => mkAppM ``Ideal.zero_mem #[I]
  let total ← memberOf hsum
  match D? with
  | none =>
      let goal ← mkFreshExprMVar (← mkEq a total)
      identity goal.mvarId!
      mkAppM ``CAS.IdealCertificate.mem_of_eq #[← instantiateMVars goal, hsum]
  | some D =>
      let lemmaApp ← mkAppOptM ``CAS.IdealCertificate.mem_of_succ_mul_mem
        #[some ctx.ring, none, none, some I, some a, some (mkNatLit D)]
      let hypType ← instantiateMVars (← inferType lemmaApp)
      let lhs := hypType.bindingDomain!.appArg!
      let goal ← mkFreshExprMVar (← mkEq lhs total)
      identity goal.mvarId!
      let h ← mkAppM ``CAS.IdealCertificate.mem_of_eq #[← instantiateMVars goal, hsum]
      return mkApp lemmaApp h

/-- Prove an equation in a commutative ring by `ring1`. -/
def ringIdentity (g : MVarId) : TermElabM Unit :=
  Mathlib.Tactic.AtomM.run .reducible (Mathlib.Tactic.Ring.proveEq g)

/-- Prove an equation in `MvPolynomial (Fin n) ℚ` by evaluating both sides at every point, which
turns the constants `C (a / b)` into rational numbers, and `ring1`. -/
def funextIdentity (g : MVarId) : TermElabM Unit := do
  let remaining ← Lean.Elab.Tactic.run g <| Lean.Elab.Tactic.evalTactic (← `(tactic|
    (apply MvPolynomial.funext; intro v
     simp only [MvPolynomial.eval_X, MvPolynomial.eval_C, map_add, map_sub, map_mul, map_neg,
       map_pow, map_one, map_zero, map_ofNat, map_natCast]
     ring1)))
  unless remaining.isEmpty do
    throwError "internal error: the identity was not proved"

/-- A proof of `Ideal.span {a₁, ..., aₙ} ≤ J` from proofs of `aᵢ ∈ J`. -/
def spanLe (members : Array Lean.Expr) : MetaM Lean.Expr := do
  let some last := members.back? | throwError "internal error: an empty set of generators"
  let mut subset ← mkAppM ``CAS.IdealCertificate.singleton_subset_of_mem #[last]
  for h in members.pop.reverse do
    subset ← mkAppM ``CAS.IdealCertificate.insert_subset_of_mem #[h, subset]
  mkAppM ``CAS.IdealCertificate.span_le_of_subset #[subset]

/-- A polynomial given to a command or found in a goal. -/
structure Input where
  /-- Its term in the ring. -/
  term : Lean.Expr
  /-- Its polynomial in the variables of the context. -/
  poly : Groebner.Poly
  /-- Whether `ring1` sees the term as `poly`: true unless the term has rational constants
  `C (a / b)`. -/
  integral : Bool
  deriving Inhabited

/-- A ring element known to lie in an ideal: the term, with the value `scale * base`, and the
proof of membership. -/
structure Fact where
  /-- The term, with integer numbers only unless it is an input. -/
  term : Lean.Expr
  /-- The polynomial of which the term is a multiple. -/
  base : Groebner.Poly
  /-- The factor between the term and `base`. -/
  scale : ℚ
  /-- The proof that the term lies in the ideal. -/
  proof : Lean.Expr
  deriving Inhabited

/-- A proof that `target`, a term with the value `targetScale * targetBase`, lies in `I`, from
`targetBase = ∑ qⱼ * baseⱼ` over facts `j`: the identity `d * target = ∑ (d * cⱼ) * termⱼ`, with
`cⱼ = targetScale / scaleⱼ * qⱼ` and `d` the least common denominator, proved by `identity`. -/
def proveFrom (ctx : Ctx) (I target : Lean.Expr) (targetScale : ℚ) (targetBase : Groebner.Poly)
    (row : Array (Fact × Groebner.Poly)) (identity : MVarId → TermElabM Unit) :
    TermElabM Lean.Expr := do
  let cofactors := (row.map fun (fact, q) ↦
      (fact, Groebner.scale (targetScale / fact.scale) q)).filter fun (_, c) ↦ !c.isEmpty
  let d := denLcm (cofactors.toList.map (·.2))
  let lhs := Groebner.scale ((d : ℚ) * targetScale) targetBase
  let rhs := cofactors.foldl (fun acc (fact, c) ↦ Groebner.add acc
    (mulPoly (Groebner.scale (d : ℚ) c) (Groebner.scale fact.scale fact.base))) []
  unless lhs == rhs do
    throwError "the cofactors do not add up to the polynomial"
  let mut summands : Array (Option Lean.Expr × Lean.Expr) := #[]
  for (fact, c) in cofactors do
    let dc := Groebner.scale (d : ℚ) c
    let coefficient? ← if isOne dc then pure none else some <$> polyExpr ctx dc
    summands := summands.push (coefficient?, fact.proof)
  combine ctx I target (if d == 1 then none else some (d - 1)) summands identity

/-- A proof that the input lies in `I` from `input.poly = ∑ qⱼ * baseⱼ` over facts `j`. An input
with rational constants is first proved as a multiple with integer coefficients. -/
def memberFrom (ctx : Ctx) (I : Lean.Expr) (input : Input) (row : Array (Fact × Groebner.Poly)) :
    TermElabM Lean.Expr := do
  if input.poly.isEmpty then
    return ← combine ctx I input.term none #[]
      (if input.integral then ringIdentity else funextIdentity)
  if input.integral then
    return ← proveFrom ctx I input.term 1 input.poly row ringIdentity
  let s := primitiveScale input.poly
  let clean ← polyExpr ctx (Groebner.scale s input.poly)
  let h ← proveFrom ctx I clean s input.poly row ringIdentity
  let inverse := Groebner.constant ctx.vars.size (1 / s)
  let coefficient? ← if isOne inverse then pure none else some <$> polyExpr ctx inverse
  combine ctx I input.term none #[(coefficient?, h)] funextIdentity

/-- The fact that an input lies in the ideal `I` of the inputs, from the proof `member` that it
belongs to the set of the inputs: the input itself when `ring1` sees it as its polynomial, and
else a multiple with coprime integer coefficients. -/
def inputFact (ctx : Ctx) (I : Lean.Expr) (input : Input) (member : Lean.Expr) :
    TermElabM Fact := do
  let proof ← mkAppM ``CAS.IdealCertificate.mem_span_of_mem #[member]
  if input.integral || input.poly.isEmpty then
    return { term := input.term, base := input.poly, scale := 1, proof }
  let s := primitiveScale input.poly
  let term ← polyExpr ctx (Groebner.scale s input.poly)
  let factor := Groebner.constant ctx.vars.size s
  let coefficient? ← if isOne factor then pure none else some <$> polyExpr ctx factor
  let proof ← combine ctx I term none #[(coefficient?, proof)] funextIdentity
  return { term, base := input.poly, scale := s, proof }

/-- Facts for the nodes `needed`, in increasing order, of a Buchberger run whose inputs have the
facts `facts`: a derived node `k` becomes `s * gₖ` with coprime integer coefficients, proved from
the facts of its derivation by `ring1`. -/
def deriveFacts (ctx : Ctx) (I : Lean.Expr) (result : Groebner.Result) (facts : Array Fact)
    (needed : List Nat) : TermElabM (Array (Option Fact)) := do
  let mut nodeFacts : Array (Option Fact) := Array.replicate result.nodes.size none
  for k in needed do
    let node := result.nodes.getD k default
    if node.input then
      nodeFacts := nodeFacts.set! k facts[k]?
    else
      let s := primitiveScale node.poly
      let term ← polyExpr ctx (Groebner.scale s node.poly)
      let mut row : Array (Fact × Groebner.Poly) := #[]
      for (j, q) in node.combo do
        let some fact := nodeFacts.getD j none |
          throwError "internal error: the derivation uses a polynomial without a proof"
        row := row.push (fact, q)
      let proof ← proveFrom ctx I term s node.poly row ringIdentity
      nodeFacts := nodeFacts.set! k (some { term, base := node.poly, scale := s, proof })
  return nodeFacts

/-- The combination of the `m` inputs that the combination `combo` of nodes stands for, through
the derivations of the nodes, or `none` when a row has more than `limit` terms. -/
def flatRow? (result : Groebner.Result) (m n : Nat) (combo : Groebner.Combo) (limit : Nat) :
    Option (Array Groebner.Poly) := Id.run do
  let size (row : Array Groebner.Poly) : Nat := row.foldl (fun a p ↦ a + p.length) 0
  let mut rows : Array (Option (Array Groebner.Poly)) := Array.replicate result.nodes.size none
  for k in result.closure (combo.map (·.1)) do
    let node := result.nodes.getD k default
    if node.input then
      rows := rows.set! k (some ((Array.range m).map fun i ↦
        if i == k then Groebner.constant n 1 else []))
    else
      let mut row : Array Groebner.Poly := Array.replicate m []
      for (j, q) in node.combo do
        let some rj := rows.getD j none | return none
        for i in [0:m] do
          row := row.set! i (Groebner.add (row.getD i []) (mulPoly q (rj.getD i [])))
      if size row > limit then return none
      rows := rows.set! k (some row)
  let mut total : Array Groebner.Poly := Array.replicate m []
  for (k, q) in combo do
    let some rk := rows.getD k none | return none
    for i in [0:m] do
      total := total.set! i (Groebner.add (total.getD i []) (mulPoly q (rk.getD i [])))
  if size total > limit then return none
  return some total

/-- A proof that `input` lies in the ideal `I` of the inputs with the facts `facts`, from the
quotients of its division by the basis of a Buchberger run on the inputs: through the
combination of the inputs when it has at most `limit` terms, and else through the derivation of
the basis. Also returns that combination when it was used. -/
def memberOfIdeal (ctx : Ctx) (I : Lean.Expr) (facts : Array Fact) (result : Groebner.Result)
    (input : Input) (quotients : Groebner.Combo) (limit : Nat := 2000) :
    TermElabM (Lean.Expr × Option (Array Groebner.Poly)) := do
  if let some row := flatRow? result facts.size ctx.vars.size quotients limit then
    let proof ← memberFrom ctx I input (facts.zip row)
    return (proof, some row)
  let nodeFacts ← deriveFacts ctx I result facts (result.closure (quotients.map (·.1)))
  let mut row : Array (Fact × Groebner.Poly) := #[]
  for (k, q) in quotients do
    let some fact := nodeFacts.getD k none |
      throwError "internal error: a basis element has no proof"
    row := row.push (fact, q)
  let proof ← memberFrom ctx I input row
  return (proof, none)

/-- The basis of a Buchberger run in decreasing order of leading monomials. -/
def sortedBasis (result : Groebner.Result) : Array Nat :=
  result.basis.toArray.insertionSort fun a b ↦
    Groebner.monoCmp (Groebner.lead (result.poly a)).1 (Groebner.lead (result.poly b)).1 == .gt

/-- The statement `Ideal.span {f₁, ..., fₘ} = Ideal.span {g₁, ..., gₖ}` for the inputs and the
basis of a Buchberger run on them, each `gᵢ` scaled to coprime integer coefficients with a
positive leading coefficient, and its proof. Also returns the scaled basis. -/
def spanEquality (ctx : Ctx) (inputs : Array Input) (result : Groebner.Result) :
    TermElabM (Array Groebner.Poly × Lean.Expr) := do
  let n := ctx.vars.size
  let (setF, fMembers) ← setLiteral ctx.ring (inputs.map (·.term))
  let idealF ← mkAppM ``Ideal.span #[setF]
  let mut facts : Array Fact := #[]
  for h : i in [0:inputs.size] do
    let fact ← inputFact ctx idealF inputs[i] fMembers[i]!
    facts := facts.push fact
  let basisNodes := sortedBasis result
  let nodeFacts ← deriveFacts ctx idealF result facts (result.closure basisNodes.toList)
  let scales := basisNodes.map fun k ↦ normalScale (result.poly k)
  let gs := (basisNodes.zip scales).map fun (k, b) ↦ Groebner.scale b (result.poly k)
  let mut gExprs : Array Lean.Expr := #[]
  for g in gs do
    let gExpr ← polyExpr ctx g
    gExprs := gExprs.push gExpr
  if gExprs.isEmpty then
    let zero ← mkNumeral ctx.ring 0
    gExprs := #[zero]
  let (setG, gMembers) ← setLiteral ctx.ring gExprs
  let idealG ← mkAppM ``Ideal.span #[setG]
  let mut gInF : Array Lean.Expr := #[]
  if basisNodes.isEmpty then
    let zeroIn ← combine ctx idealF gExprs[0]! none #[] ringIdentity
    gInF := #[zeroIn]
  for h : i in [0:basisNodes.size] do
    let k := basisNodes[i]
    let some fact := nodeFacts.getD k none |
      throwError "internal error: a basis element has no proof"
    if gExprs[i]! == fact.term then
      gInF := gInF.push fact.proof
    else
      let proof ← proveFrom ctx idealF gExprs[i]! scales[i]! (result.poly k)
        #[(fact, Groebner.constant n 1)] ringIdentity
      gInF := gInF.push proof
  let mut gFacts : Array Fact := #[]
  for h : i in [0:basisNodes.size] do
    let proof ← mkAppM ``CAS.IdealCertificate.mem_span_of_mem #[gMembers[i]!]
    gFacts := gFacts.push
      { term := gExprs[i]!, base := result.poly basisNodes[i], scale := scales[i]!, proof }
  let mut fInG : Array Lean.Expr := #[]
  for input in inputs do
    let some (remainder, quotients) := Groebner.reduce result.nodes result.basis input.poly |
      throwError "internal error: the division by the basis did not finish"
    unless remainder.isEmpty do
      throwError "internal error: an input has a nonzero remainder modulo the basis"
    let row := (basisNodes.zip gFacts).map fun (k, fact) ↦
      (fact, ((quotients.find? (·.1 == k)).map (·.2)).getD [])
    let proof ← memberFrom ctx idealG input row
    fInG := fInG.push proof
  let statement ← mkEq idealF idealG
  let proof ← mkAppM ``le_antisymm #[← spanLe fInG, ← spanLe gInF]
  return (gs, ← mkExpectedTypeHint proof statement)

/-- The statement `Ideal.span {f₁, ..., fₘ} = Ideal.span {g₁, ..., gₖ}` and its proof from
cofactors that a search proposes: `toBasis[k]` writes `gₖ` over the inputs and `fromBasis[i]`
writes `fᵢ` over the basis. Zero elements of the basis are allowed, and the empty basis of the
zero ideal is written `{0}`, as in `basisGroebnerProperty`. -/
def spanEqualityOfRows (ctx : Ctx) (inputs : Array Input) (gs : Array Groebner.Poly)
    (toBasis fromBasis : Array (Array Groebner.Poly)) : TermElabM Lean.Expr := do
  let gs := if gs.isEmpty then #[[]] else gs
  let (setF, fMembers) ← setLiteral ctx.ring (inputs.map (·.term))
  let idealF ← mkAppM ``Ideal.span #[setF]
  let mut facts : Array Fact := #[]
  for h : i in [0:inputs.size] do
    let fact ← inputFact ctx idealF inputs[i] fMembers[i]!
    facts := facts.push fact
  let mut gExprs : Array Lean.Expr := #[]
  for g in gs do
    let gExpr ← polyExpr ctx g
    gExprs := gExprs.push gExpr
  let (setG, gMembers) ← setLiteral ctx.ring gExprs
  let idealG ← mkAppM ``Ideal.span #[setG]
  let mut gInF : Array Lean.Expr := #[]
  let mut gFacts : Array Fact := #[]
  for h : k in [0:gs.size] do
    let proof ← proveFrom ctx idealF gExprs[k]! 1 gs[k] (facts.zip (toBasis.getD k #[]))
      ringIdentity
    gInF := gInF.push proof
    let member ← mkAppM ``CAS.IdealCertificate.mem_span_of_mem #[gMembers[k]!]
    gFacts := gFacts.push { term := gExprs[k]!, base := gs[k], scale := 1, proof := member }
  let mut fInG : Array Lean.Expr := #[]
  for h : i in [0:inputs.size] do
    let proof ← memberFrom ctx idealG inputs[i] (gFacts.zip (fromBasis.getD i #[]))
    fInG := fInG.push proof
  let statement ← mkEq idealF idealG
  let proof ← mkAppM ``le_antisymm #[← spanLe fInG, ← spanLe gInF]
  mkExpectedTypeHint proof statement

/-- The term of a rational number in `ℚ`. -/
def rationalLiteral (q : ℚ) : MetaM Lean.Expr := do
  let ratType := Lean.mkConst ``Rat
  let numerator ← mkNumeral ratType q.num.natAbs
  let numerator ← if q.num < 0 then mkAppM ``Neg.neg #[numerator] else pure numerator
  if q.den = 1 then return numerator
  mkAppM ``HDiv.hDiv #[numerator, ← mkNumeral ratType q.den]

/-- The terms of a polynomial in `n` variables as a list of pairs of a coefficient and the list of
the `n` exponents, the argument of `CAS.Polynomial.Sparse.ofTerms`. -/
def rawTerms (n : Nat) (p : Groebner.Poly) : MetaM Lean.Expr := do
  let natType := Lean.mkConst ``Nat
  let listNat := mkApp (Lean.mkConst ``List [Level.zero]) natType
  let ratType := Lean.mkConst ``Rat
  let termType := mkApp2 (Lean.mkConst ``Prod [Level.zero, Level.zero]) ratType listNat
  let terms ← p.mapM fun (m, c) ↦ do
    let exponents := (List.range n).map fun i ↦ mkNatLit (m.getD i 0)
    return mkApp4 (Lean.mkConst ``Prod.mk [Level.zero, Level.zero]) ratType listNat
      (← rationalLiteral c) (← mkListLit natType exponents)
  mkListLit termType terms

/-- The type `MvPoly n` of sparse polynomials in `n` variables. -/
def sparseType (n : Nat) : Lean.Expr :=
  mkApp (Lean.mkConst ``CAS.Verified.Expr.Alg.MvPoly) (mkNatLit n)

/-- The sparse polynomial `CAS.Polynomial.Sparse.ofTerms` of a polynomial in `n` variables. -/
def sparseTerm (n : Nat) (p : Groebner.Poly) : MetaM Lean.Expr := do
  return mkApp2 (Lean.mkConst ``CAS.Polynomial.Sparse.ofTerms) (mkNatLit n) (← rawTerms n p)

/-- The quotients of a division of the S-polynomial of `gs[i]` and `gs[j]` by `gs`, one for each
element of `gs`. The error is the nonzero remainder, or `none` when the division ran out of
steps. -/
def pairQuotients (gs : Array Groebner.Poly) (i j : Nat) :
    Except (Option Groebner.Poly) (Array Groebner.Poly) := do
  let nodes : Array Groebner.Node := gs.map fun g ↦ { poly := g, combo := [], input := true }
  let (mi, ci) := Groebner.lead gs[i]!
  let (mj, cj) := Groebner.lead gs[j]!
  let s := Groebner.sub (Groebner.mulTerm (Groebner.monoDiv mj mi) cj gs[i]!)
    (Groebner.mulTerm (Groebner.monoDiv mi mj) ci gs[j]!)
  let some (r, quotients) := Groebner.reduce nodes (List.range gs.size) s | throw none
  unless r.isEmpty do throw (some r)
  return (Array.range gs.size).map fun l ↦ ((quotients.find? (·.1 == l)).map (·.2)).getD []

/-- The certificate of the Gröbner property of `gs`: for every pair `i < j`, the quotients of a
division of the S-polynomial of `gs[i]` and `gs[j]` by `gs`. The error is the first pair whose
S-polynomial does not reduce to zero. -/
def groebnerCertificate (gs : Array Groebner.Poly) :
    Except (Nat × Nat × Option Groebner.Poly) (Array (Array (Array Groebner.Poly))) := do
  let mut rows := #[]
  for i in [0:gs.size] do
    let mut row := #[]
    for j in [0:gs.size] do
      if i < j then
        match pairQuotients gs i j with
        | .ok qs => row := row.push qs
        | .error r => throw (i, j, r)
      else
        row := row.push #[]
    rows := rows.push row
  return rows

/-- The term of a certificate of `groebnerCertificate`, a list of rows of lists of sparse
polynomials. -/
def certificateTerm (n : Nat) (cert : Array (Array (Array Groebner.Poly))) :
    MetaM Lean.Expr := do
  let polyType := sparseType n
  let listPolyType := mkApp (Lean.mkConst ``List [Level.zero]) polyType
  let listListType := mkApp (Lean.mkConst ``List [Level.zero]) listPolyType
  let rows ← cert.toList.mapM fun row ↦ do
    let entries ← row.toList.mapM fun qs ↦ do
      mkListLit polyType (← qs.toList.mapM (sparseTerm n))
    mkListLit listPolyType entries
  mkListLit listListType rows

/-- The function `MvPolynomial.X : Fin n → MvPolynomial (Fin n) ℚ`. -/
def variablesFunction (n : Nat) : TermElabM Lean.Expr := do
  let nT : Term := ⟨Syntax.mkNumLit (toString n)⟩
  elabClosed (← `((MvPolynomial.X : Fin $nT → MvPolynomial (Fin $nT) ℚ)))

/-- A proof of `lhs = rhs`, where `lhs` is `CAS.Polynomial.Sparse.listPolynomial xs raw` and `rhs`
is a term of the same polynomial of `MvPolynomial (Fin n) ℚ`: unfolding and `ring1`, or evaluation
at every point when constants `C q` are written differently on the two sides. When both fail, the
error names the basis element `rhs`. -/
def writtenIdentity (mode : String) (lhs rhs : Lean.Expr) : TermElabM Lean.Expr := do
  let goal ← mkFreshExprMVar (← mkEq lhs rhs)
  let saved ← Lean.Elab.Term.saveState
  try
    let remaining ← Lean.Elab.Tactic.run goal.mvarId! do
      Lean.Elab.Tactic.evalTactic (← `(tactic| simp only [CAS.Polynomial.Sparse.listPolynomial,
        CAS.Polynomial.Sparse.listMonomial, map_neg, map_ofNat, map_one, pow_zero, pow_one,
        mul_one, one_mul, add_zero]))
    for g in remaining do ringIdentity g
  catch _ =>
    saved.restore
    try
      let remaining ← Lean.Elab.Tactic.run goal.mvarId! do
        Lean.Elab.Tactic.evalTactic (← `(tactic| simp only [CAS.Polynomial.Sparse.listPolynomial,
          CAS.Polynomial.Sparse.listMonomial]))
      for g in remaining do funextIdentity g
    catch _ =>
      saved.restore
      throwError "{mode}: could not identify the basis element{indentExpr rhs}\nwith its sparse \
        form"
  instantiateMVars goal

/-- A proof of the Gröbner property for `MonomialOrder.lex` of the set literal of `gExprs` in
`MvPolynomial (Fin n) ℚ`, where `gExprs[i]` is a term of `gs[i]`. The kernel checks the
divisions of the S-polynomials (`CAS.Polynomial.Sparse.groebnerCertified`), and Buchberger's
criterion gives the property (`CAS.Polynomial.Sparse.isGroebner_of_groebnerCertified`). -/
def groebnerProperty (mode : String) (ctx : Ctx) (gs : Array Groebner.Poly)
    (gExprs : Array Lean.Expr) : TermElabM Lean.Expr := do
  let n := ctx.vars.size
  let cert ← match groebnerCertificate gs with
    | .ok cert => pure cert
    | .error (i, j, some r) => do
        throwError "{mode}: the basis is not a Gröbner basis for `MonomialOrder.lex`: the \
          S-polynomial of{indentExpr gExprs[i]!}\nand{indentExpr gExprs[j]!}\nleaves the \
          remainder{indentExpr (← polyExpr ctx r)}\non division by the basis"
    | .error (i, j, none) =>
        throwError "{mode}: the division of the S-polynomial of{indentExpr gExprs[i]!}\n\
          and{indentExpr gExprs[j]!}\nby the basis ran out of steps"
  let raws ← gs.mapM fun g ↦ rawTerms n g
  let basis ← mkListLit (sparseType n)
    (raws.toList.map (mkApp2 (Lean.mkConst ``CAS.Polynomial.Sparse.ofTerms) (mkNatLit n)))
  let statement ← mkEq (mkApp3 (Lean.mkConst ``CAS.Polynomial.Sparse.groebnerCertified)
    (mkNatLit n) basis (← certificateTerm n cert)) (Lean.mkConst ``Bool.true)
  let certified ← CAS.Tactic.KernelReadBack.decideByKernel mode statement
  let xs ← mkListLit ctx.ring ctx.vars.toList
  let hxs ← mkExpectedTypeHint (← mkEqRefl xs)
    (← mkEq (← mkAppM ``List.ofFn #[← variablesFunction n]) xs)
  let mut members : Array Lean.Expr := #[]
  for (raw, gExpr) in raws.zip gExprs do
    let lhs := mkApp3 (Lean.mkConst ``CAS.Polynomial.Sparse.listPolynomial) (mkNatLit n) xs raw
    let quoted ← mkAppM ``CAS.Polynomial.Sparse.toMvPolynomial_ofTerms #[xs, hxs, raw]
    members := members.push (← mkEqTrans quoted (← writtenIdentity mode lhs gExpr))
  let some last := members.back? | throwError "internal error: an empty basis"
  let mut hS ← mkAppM ``CAS.Polynomial.Sparse.mem_singleton_iff_exists_toMvPolynomial #[last]
  for h in members.pop.reverse do
    hS ← mkAppM ``CAS.Polynomial.Sparse.mem_insert_iff_exists_toMvPolynomial #[h, hS]
  mkAppM ``CAS.Polynomial.Sparse.isGroebner_of_groebnerCertified #[certified, hS]

/-- A proof that the basis `gs` of `#cas [groebner]`, written in `ctx` as in the span equality,
is a Gröbner basis for `MonomialOrder.lex`; the empty basis of the zero ideal is written `{0}`. -/
def basisGroebnerProperty (mode : String) (ctx : Ctx) (gs : Array Groebner.Poly) :
    TermElabM Lean.Expr := do
  let gs := if gs.isEmpty then #[[]] else gs
  let gExprs ← gs.mapM fun g ↦ polyExpr ctx g
  groebnerProperty mode ctx gs gExprs

/-- The ring and the set `S` of a goal `∀ p ∈ Ideal.span S, a ≠ b → ∃ x, c`, the goals that the
route `ideal` claims as Gröbner goals. `groebnerGoalProof` proves only the property for
`MonomialOrder.lex` and refuses the others before any division. -/
def groebnerGoal? (target : Lean.Expr) : Option (Lean.Expr × Lean.Expr) :=
  match target with
  | .forallE _ ring (.forallE _ hp (.forallE _ hp0 body _) _) _ =>
    match hp.getAppFnArgs with
    | (``Membership.mem, #[_, _, _, ideal, .bvar 0]) =>
      match ideal.getAppFnArgs with
      | (``Ideal.span, #[_, _, set]) =>
        if !set.hasLooseBVars && hp0.isAppOfArity ``Ne 3 && body.isAppOfArity ``Exists 2 then
          some (ring, set)
        else
          none
      | _ => none
    | _ => none
  | _ => none

/-- The number `n` of the ring `MvPolynomial (Fin n) ℚ`, for a numeral `n`. -/
def finVariables? (ring : Lean.Expr) : MetaM (Option Nat) := do
  let ring ← instantiateMVars ring
  match ring.getAppFnArgs with
  | (``MvPolynomial, #[σ, R, _]) =>
    unless R.isConstOf ``Rat do return none
    match σ.getAppFnArgs with
    | (``Fin, #[k]) => natLiteral? k
    | _ => return none
  | _ => return none

/-- The variable `X i` with `i < n` or the constant `C q` that an atom of a polynomial of
`MvPolynomial (Fin n) ℚ` stands for. -/
def atomImage (n : Nat) (atom : Lean.Expr) : MetaM (Verified.Expr (Fin n)) := do
  let atom ← instantiateMVars atom
  if atom.isAppOfArity ``MvPolynomial.X 4 then
    if let some i ← natLiteral? atom.appArg! then
      if h : i < n then return .var ⟨i, h⟩
  if atom.isAppOfArity ``DFunLike.coe 6 && (atom.getArg! 4).isAppOf ``MvPolynomial.C then
    let (c, inner) ← (reifyPoly atom.appArg!).run #[]
    if inner.isEmpty then
      if let some q := (poly? (overAtoms 0 c)).bind constantOf? then
        return .rat q.num q.den
  throwError "cas: {atom} is neither a variable `X i` with `i < {n}` nor a constant `C q`"

/-- The polynomial of a term of `MvPolynomial (Fin n) ℚ` built from variables `X i`, constants
`C q` and numerals by sums, differences, products, negations and powers. -/
def polynomialOver (n : Nat) (term : Lean.Expr) : MetaM Groebner.Poly := do
  let (reified, atoms) ← (reifyPoly term).run #[]
  let images ← atoms.mapM (atomImage n)
  let some p := poly? (reified.mapVars fun k ↦ images.getD k (.nat 0)) |
    throwError "cas: {term} is not a polynomial with rational coefficients"
  return p

/-- The Gröbner property for `MonomialOrder.lex` of a set `S` of `MvPolynomial (Fin n) ℚ`,
`∀ p ∈ Ideal.span S, p ≠ 0 → ∃ g ∈ S, MonomialOrder.lex.leadingTerm g ∣ …`. `groebnerGoalProof`
compares it, for the `S` that `groebnerGoal?` takes from `Ideal.span S`, with the whole goal up
to reducible definitional equality. That comparison does not identify equal sets: a goal whose
set after `∃ g ∈` lists the same polynomials in another order is refused there. -/
def lexGroebnerStatement (n : Nat) (S : Lean.Expr) : TermElabM Lean.Expr := do
  let nT : Term := ⟨Syntax.mkNumLit (toString n)⟩
  let property ← elabClosed (← `(fun S : Set (MvPolynomial (Fin $nT) ℚ) ↦
    ∀ p ∈ Ideal.span S, p ≠ 0 →
      ∃ g ∈ S, MonomialOrder.lex.leadingTerm g ∣ MonomialOrder.lex.leadingTerm p))
  return property.beta #[S]

/-- A proof of the goal `target`, the Gröbner property for `MonomialOrder.lex` of the set `set`
of the ring `ring`, both taken by `groebnerGoal?` from the outer shape of the goal. The ring must
be `MvPolynomial (Fin n) ℚ` for a numeral `n`. Then the whole goal must be
`lexGroebnerStatement n set` up to reducible definitional equality, which refuses another
monomial order, another conclusion and the same set listed in another order after `∃ g ∈`; and
`set` must be a literal that `setMembers?` reads. All of this is checked before any division. -/
def groebnerGoalProof (ring set target : Lean.Expr) : TermElabM Lean.Expr := do
  let some n ← finVariables? ring |
    throwError "cas: a Gröbner goal must be in `MvPolynomial (Fin n) ℚ` for a numeral `n`"
  let ctx ← Ctx.mvPolynomial n
  unless ← isDefEq ring ctx.ring do
    throwError "cas: a Gröbner goal must be in `MvPolynomial (Fin n) ℚ` for a numeral `n`"
  unless ← withReducible (isDefEq (← lexGroebnerStatement n set) target) do
    throwError "cas: on a goal `∀ p ∈ Ideal.span S, p ≠ 0 → ∃ …`, `cas` proves only the \
      Gröbner property for `MonomialOrder.lex`, `∃ g ∈ S, MonomialOrder.lex.leadingTerm g ∣ \
      MonomialOrder.lex.leadingTerm p` with the same set `S`; other monomial orders and other \
      conclusions are not supported"
  let some members ← setMembers? set |
    throwError "cas: the basis of a Gröbner goal must be a set literal"
  let terms := members.map (·.1)
  let polys ← terms.mapM fun t ↦ polynomialOver n t
  let proof ← groebnerProperty "cas" ctx polys terms
  unless ← isDefEq (← inferType proof) target do
    throwError "cas: the goal is not the Gröbner property for `MonomialOrder.lex`"
  return proof

/-- A monomial as text, such as `x^2*y`, or the empty string for one. -/
def monoText (names : Array String) (m : Groebner.Mono) : String :=
  "*".intercalate <| (List.range names.size).filterMap fun i ↦
    let e := m.getD i 0
    if e == 0 then none else if e == 1 then some names[i]! else some s!"{names[i]!}^{e}"

/-- A nonnegative rational number as text, such as `3/4`. -/
def ratText (q : ℚ) : String :=
  if q.den == 1 then toString q.num else s!"{q.num}/{q.den}"

/-- A term with a nonnegative coefficient as text, such as `3/4*x*y^2`. -/
def termText (names : Array String) (m : Groebner.Mono) (c : ℚ) : String :=
  let mono := monoText names m
  if mono.isEmpty then ratText c
  else if c == 1 then mono
  else s!"{ratText c}*{mono}"

/-- A polynomial as text, in decreasing lexicographic order, such as `x^2 - 1/2*y + 3`. -/
def renderPoly (names : Array String) (p : Groebner.Poly) : String := Id.run do
  let mut out := ""
  for (m, c) in p do
    let t := termText names m (if c < 0 then -c else c)
    if out.isEmpty then
      out := if c < 0 then s!"-{t}" else t
    else
      out := out ++ (if c < 0 then s!" - {t}" else s!" + {t}")
  return if out.isEmpty then "0" else out

/-- The combination `∑ cᵢ * gᵢ` as text, with the generators as written. -/
def combinationText (names generators : Array String) (cofactors : Array Groebner.Poly) :
    String := Id.run do
  let wrap (s : String) : String :=
    if s.any (fun ch ↦ ch == ' ' || ch == '+' || ch == '-') then s!"({s})" else s
  let mut out := ""
  for h : i in [0:cofactors.size] do
    let c := cofactors[i]
    if c.isEmpty then continue
    let g := wrap generators[i]!
    let (negative, body) := match c with
      | [(m, k)] =>
          if Groebner.degree m == 0 && (k == 1 || k == -1) then (decide (k < 0), g)
          else (decide (k < 0), s!"{termText names m (if k < 0 then -k else k)}*{g}")
      | _ => (false, s!"({renderPoly names c})*{g}")
    if out.isEmpty then
      out := if negative then s!"-{body}" else body
    else
      out := out ++ (if negative then s!" - {body}" else s!" + {body}")
  return if out.isEmpty then "0" else out

/-- The polynomial of a term in the variables `names`, as an input in the context
`MvPolynomial (Fin n) ℚ`. -/
def readPolynomial (ctx : Ctx) (mode : String) (names : Array Name) (stx : Syntax) :
    TermElabM Input := do
  let reified ← parseExact stx names.toList
  let n := names.size
  if h : reified.names.length = n then
    let expr : Verified.Expr (Fin n) := h ▸ reified.expr
    let some poly := poly? expr |
      throwErrorAt stx "{mode}: {surfaceText stx} is not a polynomial with rational coefficients"
    let (term, integral) ← typedExpr ctx expr
    return { term, poly, integral }
  else
    throwErrorAt stx "{mode}: {surfaceText stx} mentions symbols other than \
      {renderNames names.toList}"

/-- The domain line of the reports, such as
`ℚ[x, y] as MvPolynomial (Fin 2) ℚ, with x = X 0, y = X 1`. -/
def domainText (names : Array Name) : String :=
  let shown := names.toList.map renderName
  let joined := String.intercalate ", " shown
  let pairs := (List.range shown.length).zip shown
  let bindings := String.intercalate ", " (pairs.map fun (i, x) ↦ s!"{x} = X {i}")
  s!"ℚ[{joined}] as MvPolynomial (Fin {names.size}) ℚ, with {bindings}"

/-- Run `x` with the namespace `MvPolynomial` open, so that the variables print as `X i`. -/
def withMvPolynomialNames {α : Type} (x : TermElabM α) : TermElabM α :=
  withTheReader Core.Context
    (fun c ↦ { c with openDecls := .simple `MvPolynomial [] :: c.openDecls }) x

/-- Log a report with the namespace `MvPolynomial` open. -/
def logIdealReport (ref : Syntax) (summary : ReportSummary) (details : Array MessageData) :
    CommandElabM Unit :=
  withScope (fun scope ↦ { scope with openDecls := .simple `MvPolynomial [] :: scope.openDecls })
    (logReport ref summary details)

/-- The Buchberger run of `mode` on the inputs, with its error as a refusal. -/
def runBuchberger (ref : Syntax) (mode : String) (inputs : Array Input) :
    TermElabM Groebner.Result := do
  match Groebner.groebner (inputs.map (·.poly)).toList with
  | .ok result => return result
  | .error reason =>
      if mode == "groebner" then
        throwErrorAt ref "groebner: {reason}; `#cas [groebner …, oracle := o]` with CASOracle \
          asks an external system instead"
      else
        throwErrorAt ref "{mode}: {reason}"

/-- Run `#cas [groebner x, y] [f₁, ..., fₘ]`. -/
def logGroebner (ref : Syntax) (variableIds : Array (TSyntax `ident))
    (polynomials : Array Term) : CommandElabM Unit := do
  let names := variableIds.map (·.getId)
  let shown := names.map renderName
  let (gs, proof, groebner, size) ← liftTermElabM <| PolySystems.withProofBudget do
    let ctx ← Ctx.mvPolynomial names.size
    let inputs ← polynomials.mapM fun p ↦ readPolynomial ctx "groebner" names p
    let result ← runBuchberger ref "groebner" inputs
    let (gs, proof) ← spanEquality ctx inputs result
    let groebner ← basisGroebnerProperty "groebner" ctx gs
    return (gs, proof, groebner, (result.closure result.basis).length)
  let report ← liftTermElabM <| withMvPolynomialNames do
    let step ← CAS.Tactic.Explanation.UncheckedExplanationStep.ofProof "Ideal of the inputs" proof
    let basisStep ← CAS.Tactic.Explanation.UncheckedExplanationStep.ofProof
      "Gröbner property of the basis" groebner
    evidenceReportMessage #[step, basisStep]
  let output := if gs.isEmpty then "0" else ", ".intercalate (gs.toList.map (renderPoly shown))
  let order := " > ".intercalate shown.toList
  logIdealReport ref {
    domain := domainText names
    input := ", ".intercalate (polynomials.toList.map fun p ↦ surfaceText p)
    inputType := "polynomials"
    output := output
    outputType := "Gröbner basis of the same ideal (checked)"
  } #[computationNode "Gröbner basis" #[m!"the reduced basis for the lexicographic order \
      {order}, each element scaled to coprime integer coefficients with a positive leading \
      coefficient; computed by SymLean's Buchberger algorithm, {size} polynomials in the \
      derivation, {gs.size} in the basis"], report]

/-- Run `#cas [member x, y] f [g₁, ..., gₘ]`. -/
def logMember (ref : Syntax) (variableIds : Array (TSyntax `ident)) (element : Term)
    (generators : Array Term) : CommandElabM Unit := do
  let names := variableIds.map (·.getId)
  let shown := names.map renderName
  let elementText := if element.raw.isOfKind ``Lean.Parser.Term.paren then
      surfaceText element.raw[1] else surfaceText element
  let (target, cofactors?, proof) ← liftTermElabM <| PolySystems.withProofBudget do
    let ctx ← Ctx.mvPolynomial names.size
    let target ← readPolynomial ctx "member" names element
    let inputs ← generators.mapM fun g ↦ readPolynomial ctx "member" names g
    let result ← runBuchberger ref "member" inputs
    let some (remainder, quotients) := Groebner.reduce result.nodes result.basis target.poly |
      throwErrorAt ref "member: the division by the basis did not finish"
    unless remainder.isEmpty do
      throwErrorAt ref "member: {elementText} is not shown to be in the ideal: its remainder \
        modulo the computed lexicographic basis is {renderPoly shown remainder}. The basis is not \
        proved to be a Gröbner basis, so this proves nothing about non-membership"
    let (set, members) ← setLiteral ctx.ring (inputs.map (·.term))
    let ideal ← mkAppM ``Ideal.span #[set]
    let mut facts : Array Fact := #[]
    for h : i in [0:inputs.size] do
      let fact ← inputFact ctx ideal inputs[i] members[i]!
      facts := facts.push fact
    let (proof, cofactors?) ← memberOfIdeal ctx ideal facts result target quotients
    let statement ← mkAppM ``Membership.mem #[ideal, target.term]
    return (target, cofactors?, ← mkExpectedTypeHint proof statement)
  let report ← liftTermElabM <| withMvPolynomialNames do
    let step ← CAS.Tactic.Explanation.UncheckedExplanationStep.ofProof
      "Membership in the ideal of the generators" proof
    evidenceReportMessage #[step]
  let generatorTexts := generators.map fun g ↦ surfaceText g
  let combination := match cofactors? with
    | some cofactors => combinationText shown generatorTexts cofactors
    | none => "a combination of the generators with cofactors of more than 2000 terms"
  logIdealReport ref {
    domain := domainText names
    input := s!"{elementText} and ⟨{", ".intercalate generatorTexts.toList}⟩"
    inputType := "polynomial and ideal"
    output := s!"{renderPoly shown target.poly} = {combination}"
    outputType := "a combination of the generators (checked)"
  } #[report]

/-- The ring and the generators of an ideal `Ideal.span {g₁, ..., gₘ}`, each with a proof that it
lies in the ideal. -/
def spanGenerators? (ideal : Lean.Expr) :
    MetaM (Option (Lean.Expr × Array (Lean.Expr × Lean.Expr))) := do
  let ideal ← instantiateMVars ideal
  match ideal.getAppFnArgs with
  | (``Ideal.span, #[ring, inst, set]) =>
      let some members ← setMembers? set | return none
      let mut result : Array (Lean.Expr × Lean.Expr) := #[]
      for (g, h) in members do
        let proof ← mkAppOptM ``CAS.IdealCertificate.mem_span_of_mem
          #[some ring, some inst, some set, some g, some h]
        result := result.push (g, proof)
      return some (ring, result)
  | _ => return none

/-- The polynomials of ring elements over their shared atoms, and the context with the atoms as
variables. -/
def reifyTerms (ring : Lean.Expr) (terms : Array Lean.Expr) :
    MetaM (Ctx × Array Groebner.Poly) := do
  let (exprs, atoms) ← (terms.mapM reifyPoly).run #[]
  let mut polys : Array Groebner.Poly := #[]
  for reified in exprs do
    let some p := poly? (overAtoms atoms.size reified) |
      throwError "cas: an element of the ideal goal is not a polynomial in its atoms"
    polys := polys.push p
  let ctx ← Ctx.ofRing ring atoms
  return (ctx, polys)

/-- Proofs that the targets lie in the ideal `I` of the generators, whose memberships are
`facts`, from one Buchberger run on the generators. -/
def membersOf (ctx : Ctx) (I : Lean.Expr) (generators : Array Input) (facts : Array Fact)
    (targets : Array Input) : TermElabM (Array Lean.Expr) := do
  let result ← runBuchberger (← getRef) "cas" generators
  targets.mapM fun target ↦ do
    let some (remainder, quotients) := Groebner.reduce result.nodes result.basis target.poly |
      throwError "cas: the division by the Gröbner basis did not finish"
    unless remainder.isEmpty do
      throwError "cas: {target.term} is not shown to be in the ideal: its remainder modulo the \
        computed lexicographic basis is not zero. The basis is not proved to be a Gröbner basis, \
        so this proves nothing about non-membership"
    let (proof, _) ← memberOfIdeal ctx I facts result target quotients
    return proof

/-- The inputs and facts of the generators of an ideal goal, at scale one: `ring1` sees each
generator as its polynomial over the atoms. -/
def generatorFacts (generators : Array (Lean.Expr × Lean.Expr)) (polys : Array Groebner.Poly) :
    Array Input × Array Fact :=
  let inputs := (generators.zip polys).map fun ((g, _), p) ↦
    ({ term := g, poly := p, integral := true } : Input)
  let facts := (generators.zip polys).map fun ((g, h), p) ↦
    ({ term := g, base := p, scale := 1, proof := h } : Fact)
  (inputs, facts)

/-- A proof of `f ∈ Ideal.span {g₁, ..., gₘ}` or
`Ideal.span {f₁, ..., fₘ} = Ideal.span {g₁, ..., gₖ}` in a commutative ring, or of the Gröbner
property `∀ p ∈ Ideal.span S, p ≠ 0 → ∃ g ∈ S, MonomialOrder.lex.leadingTerm g ∣ …` of a set
literal `S` in `MvPolynomial (Fin n) ℚ`. -/
def idealGoalProof (target : Lean.Expr) : TermElabM Lean.Expr := do
  let target := (← instantiateMVars target).consumeMData
  match target.getAppFnArgs with
  | (``Membership.mem, #[_, _, _, ideal, element]) =>
      let some (ring, generators) ← spanGenerators? ideal |
        throwError "cas: the ideal is not `Ideal.span` of a set literal"
      let (ctx, polys) ← reifyTerms ring (#[element] ++ generators.map (·.1))
      let (inputs, facts) := generatorFacts generators (polys.extract 1 polys.size)
      let member : Input := { term := element, poly := polys[0]!, integral := true }
      let proofs ← membersOf ctx ideal inputs facts #[member]
      return proofs[0]!
  | (``Eq, #[_, lhs, rhs]) =>
      let some (ring, fs) ← spanGenerators? lhs |
        throwError "cas: the left side is not `Ideal.span` of a set literal"
      let some (_, gs) ← spanGenerators? rhs |
        throwError "cas: the right side is not `Ideal.span` of a set literal"
      let (ctx, polys) ← reifyTerms ring (fs.map (·.1) ++ gs.map (·.1))
      let (fInputs, fFacts) := generatorFacts fs (polys.extract 0 fs.size)
      let (gInputs, gFacts) := generatorFacts gs (polys.extract fs.size polys.size)
      let fInG ← membersOf ctx rhs gInputs gFacts fInputs
      let gInF ← membersOf ctx lhs fInputs fFacts gInputs
      mkAppM ``le_antisymm #[← spanLe fInG, ← spanLe gInF]
  | _ =>
      match groebnerGoal? target with
      | some (ring, set) => groebnerGoalProof ring set target
      | none => throwError "cas: not an ideal goal"

/-- Whether a term is a set literal `{a₁, ..., aₙ}`. -/
def isSetLiteral (s : Lean.Expr) : Bool :=
  s.isAppOfArity ``Insert.insert 5 || s.isAppOfArity ``Singleton.singleton 4

/-- Whether a term is `Ideal.span` of a set literal. -/
def isSpanOfLiteral (e : Lean.Expr) : Bool :=
  e.isAppOfArity ``Ideal.span 3 && isSetLiteral e.appArg!

/-- The goals of the route `ideal`: `f ∈ Ideal.span {g₁, ..., gₘ}`,
`Ideal.span {f₁, ..., fₘ} = Ideal.span {g₁, ..., gₖ}` and `∀ p ∈ Ideal.span S, p ≠ 0 → ∃ x, …`,
of which the route proves only the Gröbner property for `MonomialOrder.lex`. -/
def isIdealGoal : CAS.Tactic.RouteRegistry.GoalPredicate := fun target ↦ do
  let target := (← instantiateMVars target).consumeMData
  match target.getAppFnArgs with
  | (``Membership.mem, #[_, _, _, ideal, _]) => return isSpanOfLiteral ideal
  | (``Eq, #[_, lhs, rhs]) => return isSpanOfLiteral lhs && isSpanOfLiteral rhs
  | _ => return (groebnerGoal? target).isSome

/-- The route `ideal` of `cas`: a goal `f ∈ Ideal.span {g₁, ..., gₘ}` or
`Ideal.span {f₁, ..., fₘ} = Ideal.span {g₁, ..., gₖ}` in a commutative ring, proved from a
Buchberger run on the generators over the atoms of the goal, or the Gröbner property
`∀ p ∈ Ideal.span S, p ≠ 0 → ∃ g ∈ S, MonomialOrder.lex.leadingTerm g ∣ …` of a set literal `S`
in `MvPolynomial (Fin n) ℚ`, proved from the divisions of its S-polynomials. The kernel checks
the proof. The property for another monomial order is refused before any division. -/
@[cas_route ideal (priority := 1950) (goal := isIdealGoal)]
def idealRoute : CAS.Tactic.RouteRegistry.Closer := fun _ ↦ do
  let description := "cas on an ideal goal"
  CAS.Tactic.ProofCarrier.withKernelOnlyAxioms description do
    Lean.Elab.Tactic.withMainContext do
      let goal ← Lean.Elab.Tactic.getMainGoal
      let target ← instantiateMVars (← goal.getType)
      if target.hasMVar then
        throwError "cas: the ideal goal has metavariables"
      let proof ← idealGoalProof target
      let checked ← CAS.Tactic.Explanation.kernelCheckedProof description target proof
      goal.assign checked
      Lean.Elab.Tactic.replaceMainGoal []
      return ((), #[])
  return {
    replay := ← `(tactic| cas)
    plannerMetadata := #[{
      label := "ideal certificate from SymLean's Buchberger algorithm, checked by the kernel"
      status := .selected
    }]
  }

end CAS.Command.Ideal

namespace CAS.Command

open Lean Elab Command

/-- `#cas [groebner x, y] [f₁, …, fₘ]` computes the reduced Gröbner basis of the polynomials
`f₁, …, fₘ` for the lexicographic order `x > y`, prints it with each element scaled to coprime
integer coefficients and a positive leading coefficient, and proves that it generates the same
ideal and is a Gröbner basis.

## Theorem
The report proves two propositions in `MvPolynomial (Fin n) ℚ`, where the `i`-th listed variable
is `X i`. The first is `Ideal.span {f₁, …, fₘ} = Ideal.span {g₁, …, gₖ}`: every `gⱼ` is a
combination of the inputs and every input a combination of the `gⱼ`, with explicit cofactors
checked by `ring`. The second is the Gröbner property for `MonomialOrder.lex`, with `X 0` the
largest variable:
`∀ p ∈ Ideal.span {g₁, …, gₖ}, p ≠ 0 → ∃ g ∈ {g₁, …, gₖ}, MonomialOrder.lex.leadingTerm g ∣
MonomialOrder.lex.leadingTerm p`. It follows from Buchberger's criterion
(`CAS.Polynomial.Buchberger`) and a division of the S-polynomial of every pair of the `gⱼ` by the
basis, which the kernel checks (`CAS.Polynomial.Sparse.groebnerCertified`). That the basis is the
reduced one is not proved.

## Conditions and limits
The inputs are polynomials in the listed variables with rational coefficients; division is
allowed by nonzero constants only. The zero ideal has the empty basis, printed `0` and written
`{0}` in the theorems. The search stops after 400 polynomials or 4000 pairs.

## Options
None.

## Examples
```lean
#cas [groebner x, y] [x^2 + y^2 - 5, x*y - 2]
```
```output
Output (Gröbner basis of the same ideal (checked)): 2*x + y^3 - 5*y, y^4 - 5*y^2 + 4
```
```lean
#cas [groebner x, y, z] [x^2 + y^2 + z^2 - 1, x^2 + z^2 - y, x - z]
```
```output
Output (Gröbner basis of the same ideal (checked)): x - z, y - 2*z^2, 4*z^4 + 2*z^2 - 1
```
```lean
#cas [groebner x, y] [x*y - 1, x]
```
```output
Output (Gröbner basis of the same ideal (checked)): 1
```

## In a proof
```lean
open MvPolynomial in
theorem groebner_span :
    Ideal.span {(X 0 ^ 2 + X 1 ^ 2 - 5 : MvPolynomial (Fin 2) ℚ), X 0 * X 1 - 2} =
      Ideal.span {2 * X 0 + X 1 ^ 3 - 5 * X 1, X 1 ^ 4 - 5 * X 1 ^ 2 + 4} := by
  cas
```
The tactic `cas` also proves the Gröbner property of a set literal of `MvPolynomial (Fin n) ℚ`:
```lean
open MvPolynomial in
theorem groebner_basis :
    ∀ p ∈ Ideal.span ({2 * X 0 + X 1 ^ 3 - 5 * X 1, X 1 ^ 4 - 5 * X 1 ^ 2 + 4} :
        Set (MvPolynomial (Fin 2) ℚ)), p ≠ 0 →
      ∃ g ∈ ({2 * X 0 + X 1 ^ 3 - 5 * X 1, X 1 ^ 4 - 5 * X 1 ^ 2 + 4} :
        Set (MvPolynomial (Fin 2) ℚ)),
        MonomialOrder.lex.leadingTerm g ∣ MonomialOrder.lex.leadingTerm p := by
  cas
```

## See also
Mathematica `GroebnerBasis`, SymPy `groebner`. The modes `member` and `solve x, y`. Oracle route:
`#cas [groebner x, y, oracle := sage] [f₁, …, fₘ]`, which asks Sage or SymPy for the basis and
checks it in the same way.

## Possible issues
```lean
#cas [groebner x, y] [x^2 + z, y]
```
```output
expression contains undeclared variables: z
```
List every variable of the inputs after the mode name.
```lean
#cas [groebner x, y] [x^2 + sin y, y]
```
```output
groebner: x^2 + sin y is not a polynomial with rational coefficients
```
The inputs must be polynomials. A long search fails with "groebner: the Gröbner basis exceeded
its budget"; the oracle route can then take over. On a Gröbner goal, `cas` refuses a set that is
not a Gröbner basis for `MonomialOrder.lex` and names a pair whose S-polynomial leaves a nonzero
remainder. Before any division it reads the goal in three steps. The shape
`∀ p ∈ Ideal.span S, a ≠ b → ∃ x, c` is matched as written, without unfolding definitions. The
whole goal is then compared with the property for `MonomialOrder.lex` and this `S` up to reducible
definitional equality, which refuses another monomial order or another conclusion, and also the
set after `∃ g ∈` listed in another order, since the two occurrences are compared as terms and
not as sets. Last, `S` must be a set literal such as `{g₁, g₂}`, read without unfolding, so a
`Finset` coercion, a set behind a definition and the empty set are refused.
-/
syntax (name := casGroebnerCommand) "#cas" "[" &"groebner" ident,+ "]" "[" term,+ "]" : command

/-- `#cas [member x, y] f [g₁, …, gₘ]` proves that the polynomial `f` lies in the ideal generated by
`g₁, …, gₘ` and prints `f` as a combination of the generators.

## Theorem
The report proves `f ∈ Ideal.span {g₁, …, gₘ}` in `MvPolynomial (Fin n) ℚ`, where the `i`-th
listed variable is `X i`, by explicit cofactors checked by `ring`.

## Conditions and limits
`f` and the generators are polynomials in the listed variables with rational coefficients. The
cofactors come from the division of `f` by the reduced lexicographic Gröbner basis of the
generators and from the derivation of that basis. When they have more than 2000 terms, the proof
goes through the basis and the output says only that they have more than 2000 terms.

## Options
None.

## Examples
```lean
#cas [member x, y] (x^2 - 1) [x*y - 1, x - y]
```
```output
Output (a combination of the generators (checked)): x^2 - 1 = (x*y - 1) + x*(x - y)
```
```lean
#cas [member x, y, z] (x^3 - y^3) [x - y, z]
```
```output
Output (a combination of the generators (checked)): x^3 - y^3 = (x^2 + x*y + y^2)*(x - y)
```

## In a proof
```lean
theorem mem_span_real (a b : ℝ) : a ^ 2 - 1 ∈ Ideal.span {a * b - 1, a - b} := by
  cas
```

## See also
Mathematica `PolynomialReduce`, SymPy `reduced`. The mode `groebner`, and the tactic `cas`, which
proves `f ∈ Ideal.span {g₁, …, gₘ}` in a commutative ring; a certificate with denominators needs
a ℚ-algebra. Oracle route: `cas [oracle := o]`, which asks Sage or SymPy for the cofactors.

## Possible issues
```lean
#cas [member x, y] x [x^2, y]
```
```output
member: x is not shown to be in the ideal: its remainder modulo the computed lexicographic basis
is x. The basis is not proved to be a Gröbner basis, so this proves nothing about non-membership
```
A nonzero remainder proves nothing about non-membership; `x` is in fact outside this ideal.
-/
syntax (name := casMemberCommand) "#cas" "[" &"member" ident,+ "]" term:max "[" term,+ "]" :
  command

elab_rules : command
  | `(#cas [groebner $xs:ident,*] [$ps:term,*]) => do
      Ideal.logGroebner (← getRef) xs.getElems ps.getElems
  | `(#cas [member $xs:ident,*] $f:term [$gs:term,*]) => do
      Ideal.logMember (← getRef) xs.getElems f gs.getElems

end CAS.Command
