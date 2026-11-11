/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Calculus.ConditionFree
public import CAS.Command.Series
public meta import CAS.Calculus.ConditionFree

/-!
# Exponential polynomials and undetermined coefficients

The right sides of `#cas [dsolve y x]` and the functions of `#cas [fourier x n]` are exponential
polynomials `∑ e ^ (λ x) P_λ (x)` with Gaussian rational `λ` and coefficients (`ExpPoly`, read
from an expression by `toExpPoly`). For a characteristic polynomial `p`, `particular` finds a
particular solution of `p (D) y = f` by undetermined coefficients: for each `λ` it solves
`p (D + λ) g = P_λ` (`solveShifted`) and returns the real part `Re ∑ e ^ (λ x) g_λ (x)` as an
expression. The helpers `real` and `surd` write a rational and `a + b √n` as real terms,
`solutionRhs` reads the right side of a solution formula, and the lemmas `cleanLemmas` restate
evaluation in ordinary notation.

## Implementation notes

We write `p (D + λ) = ∑ c_j D ^ j` with `c_j = p ^ (j) (λ) / j!` (`shifted`); the first nonzero
`c_s` sits at the multiplicity `s` of `λ` as a root of `p`. `solveShifted` solves
`∑ c_(s + i) D ^ i G = P_λ` by back substitution from the top degree and integrates `G` `s`
times without constants, so `g_λ` has degree `deg P_λ + s` and no terms below `x ^ s`.
`particular` collects the terms by `(Re λ, |Im λ|)` and writes the real part with `cos` and
`sin`. The form of the solution, `e ^ (λ x)` times a polynomial whose degree is raised by the
multiplicity of `λ`, is classical. The search is ours and untrusted, in Gaussian rational
arithmetic: `#cas [dsolve y x]` checks the particular solution by an identity between symbolic
derivatives (`CAS/Command/DSolveOrder.lean` and `CAS/Command/DSolveRoot.lean`, with
`CAS.LinearODE.iteratedDeriv_univariateEval` and `ring_nf`).

## References

* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems*, Graduate Studies in
  Mathematics 140, American Mathematical Society, Providence, 2012,
  <https://doi.org/10.1090/gsm/140>. Lemma 3.8 (§3.3) of the author's online version,
  <https://www.mat.univie.ac.at/~gerald/ftp/book-ode/>, and the remarks after it, for the form of
  the particular solution.
-/

public meta section

namespace CAS.Command.ExpPolynomials

open Lean Elab Command Meta Term

/-! ## Gaussian rationals and exponential polynomials -/

/-- A Gaussian rational `re + i im`. -/
structure GaussianRat where
  /-- The real part. -/
  re : ℚ
  /-- The imaginary part. -/
  im : ℚ
  deriving BEq, Inhabited

namespace GaussianRat

/-- `q + 0 i`. -/
def ofRat (q : ℚ) : GaussianRat := ⟨q, 0⟩
/-- Addition of Gaussian rationals, componentwise. -/
instance : Add GaussianRat := ⟨fun a b ↦ ⟨a.re + b.re, a.im + b.im⟩⟩
/-- Subtraction of Gaussian rationals, componentwise. -/
instance : Sub GaussianRat := ⟨fun a b ↦ ⟨a.re - b.re, a.im - b.im⟩⟩
/-- Negation of Gaussian rationals, componentwise. -/
instance : Neg GaussianRat := ⟨fun a ↦ ⟨-a.re, -a.im⟩⟩
/-- Complex multiplication: `(a + i b) (c + i d) = (a c - b d) + i (a d + b c)`. -/
instance : Mul GaussianRat := ⟨fun a b ↦ ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩⟩
/-- `1 / a = (re - i im) / (re ^ 2 + im ^ 2)`, which is `0` for `a = 0`. -/
def inv (a : GaussianRat) : GaussianRat :=
  let n := a.re * a.re + a.im * a.im
  ⟨a.re / n, -a.im / n⟩
/-- Division `a / b = a * b.inv`, which is `0` for `b = 0`. -/
instance : Div GaussianRat := ⟨fun a b ↦ a * b.inv⟩
/-- Whether `a = 0`. -/
def isZero (a : GaussianRat) : Bool := a.re == 0 && a.im == 0

end GaussianRat

/-- Coefficients of `x ^ k`. -/
abbrev CPoly := Array GaussianRat

/-- `a + b`, coefficientwise. -/
def cpAdd (a b : CPoly) : CPoly :=
  (Array.range (max a.size b.size)).map fun k ↦ a.getD k default + b.getD k default

/-- `c a`. -/
def cpScale (c : GaussianRat) (a : CPoly) : CPoly := a.map (c * ·)

/-- `a b`, and `#[]` when `a` or `b` is `#[]`. -/
def cpMul (a b : CPoly) : CPoly := Id.run do
  if a.isEmpty || b.isEmpty then return #[]
  let mut out : CPoly := Array.replicate (a.size + b.size - 1) default
  for i in [0:a.size] do
    for j in [0:b.size] do
      out := out.set! (i + j) (out.getD (i + j) default + a.getD i default * b.getD j default)
  return out

/-- All coefficients are zero. -/
def cpIsZero (a : CPoly) : Bool := a.all GaussianRat.isZero

/-- `∑ e ^ (λ x) P_λ (x)`. -/
abbrev ExpPoly := List (GaussianRat × CPoly)

/-- `a + b` when the terms of `a` have distinct `λ`: the polynomials of equal `λ` are added and
zero terms dropped. -/
def epAdd (a b : ExpPoly) : ExpPoly :=
  let merged := b.foldl (fun total (l, p) ↦
    match total.find? (·.1 == l) with
    | some (_, q) => total.filter (·.1 != l) ++ [(l, cpAdd q p)]
    | none => total ++ [(l, p)]) a
  merged.filter fun (_, p) ↦ !cpIsZero p

/-- `c a`. -/
def epScale (c : GaussianRat) (a : ExpPoly) : ExpPoly := a.map fun (l, p) ↦ (l, cpScale c p)

/-- `a b`: the products `e ^ ((λ₁ + λ₂) x) P₁ P₂` of all pairs of terms, summed by
`epAdd`. -/
def epMul (a b : ExpPoly) : ExpPoly :=
  a.foldl (fun total (l₁, p₁) ↦
    b.foldl (fun total (l₂, p₂) ↦ epAdd total [(l₁ + l₂, cpMul p₁ p₂)]) total) []

/-- The constant `q` as `e ^ (0 x) q`, and `[]` for `q = 0`. -/
def epConst (q : ℚ) : ExpPoly := if q = 0 then [] else [(default, #[GaussianRat.ofRat q])]

/-- The constant of an exponential polynomial without exponential or `x`. -/
def epConstant? (a : ExpPoly) : Option ℚ :=
  match a with
  | [] => some 0
  | [(l, p)] =>
      if l.isZero && (List.range p.size).all (fun k ↦ k == 0 || (p.getD k default).isZero) &&
        (p.getD 0 default).im == 0 then some (p.getD 0 default).re else none
  | _ => none

/-- The slope `c` of an exponential polynomial `c x`. -/
def epLinear? (a : ExpPoly) : Option ℚ :=
  match a with
  | [] => some 0
  | [(l, p)] =>
      if l.isZero && (p.getD 0 default).isZero && (p.getD 1 default).im == 0 &&
        (List.range p.size).all (fun k ↦ k ≤ 1 || (p.getD k default).isZero) then
        some (p.getD 1 default).re
      else none
  | _ => none

/-- The exponential polynomial of an expression in `x`. -/
partial def toExpPoly : Verified.Expr (Fin 1) → Option ExpPoly
  | .nat n => some (epConst n)
  | .int n => some (epConst n)
  | .rat p q => if q = 0 then none else some (epConst ((p : ℚ) / q))
  | .var _ => some [(default, #[default, GaussianRat.ofRat 1])]
  | .add a b => return epAdd (← toExpPoly a) (← toExpPoly b)
  | .sub a b => return epAdd (← toExpPoly a) (epScale (GaussianRat.ofRat (-1)) (← toExpPoly b))
  | .neg a => return epScale (GaussianRat.ofRat (-1)) (← toExpPoly a)
  | .mul a b => return epMul (← toExpPoly a) (← toExpPoly b)
  | .pow a n => do
      let base ← toExpPoly a
      return (List.range n).foldl (fun total _ ↦ epMul total base) (epConst 1)
  | .div a b => do
      let c ← epConstant? (← toExpPoly b)
      if c = 0 then none
      return epScale (GaussianRat.ofRat (1 / c)) (← toExpPoly a)
  | .exp a => do
      let c ← epLinear? (← toExpPoly a)
      return [(GaussianRat.ofRat c, #[GaussianRat.ofRat 1])]
  | .cos a => do
      let b ← epLinear? (← toExpPoly a)
      if b = 0 then return epConst 1
      return [(⟨0, b⟩, #[GaussianRat.ofRat (1 / 2)]), (⟨0, -b⟩, #[GaussianRat.ofRat (1 / 2)])]
  | .sin a => do
      let b ← epLinear? (← toExpPoly a)
      if b = 0 then return []
      return [(⟨0, b⟩, #[⟨0, -1 / 2⟩]), (⟨0, -b⟩, #[⟨0, 1 / 2⟩])]
  | _ => none

/-! ## Undetermined coefficients -/

/-- The binomial coefficient `n.choose k`, as a rational. -/
def choose (n k : Nat) : ℚ := (Nat.choose n k : ℚ)

/-- `p ^ (j) (λ) / j!` for `j = 0, …, n`, where `p = ∑ a_k z ^ k`. -/
def shifted (a : Array ℚ) (l : GaussianRat) : Array GaussianRat :=
  (Array.range a.size).map fun j ↦
    (List.range a.size).foldl (fun total k ↦
      if k < j then total else
      let power := (List.range (k - j)).foldl (fun acc _ ↦ acc * l) (GaussianRat.ofRat 1)
      total + GaussianRat.ofRat (a.getD k 0 * choose k j) * power) default

/-- The polynomial `g` with `p (D + λ) g = P`, of degree raised by the multiplicity of `λ`. -/
def solveShifted (a : Array ℚ) (l : GaussianRat) (P : CPoly) : Option CPoly := do
  let c := shifted a l
  let s ← (List.range c.size).find? fun j ↦ !(c.getD j default).isZero
  let m := P.size
  let mut G : CPoly := Array.replicate m default
  for offset in [0:m] do
    let k := m - 1 - offset
    let mut rest := P.getD k default
    for i in [1:m - k] do
      let factor : ℚ := (List.range i).foldl (fun acc t ↦ acc * (k + i - t : ℕ)) 1
      rest := rest - c.getD (s + i) default * GaussianRat.ofRat factor * G.getD (k + i) default
    G := G.set! k (rest / c.getD s default)
  -- `g = s`-fold antiderivative of `G` without constants.
  let mut g : CPoly := Array.replicate (m + s) default
  for k in [0:m] do
    let factor : ℚ := (List.range s).foldl (fun acc t ↦ acc / (k + s - t : ℕ)) 1
    g := g.set! (k + s) (GaussianRat.ofRat factor * G.getD k default)
  return g

/-- An expression for a rational. -/
def ratExpr (q : ℚ) : Verified.Expr (Fin 1) :=
  if q.den = 1 then (if 0 ≤ q.num then .nat q.num.toNat else .int q.num) else .rat q.num q.den

/-- `q x` as an expression. -/
def linearExpr (q : ℚ) : Verified.Expr (Fin 1) :=
  if q = 1 then .var 0 else .mul (ratExpr q) (.var 0)

/-- `∑ c_k x ^ k`. -/
def polyExpr (cs : Array ℚ) : Option (Verified.Expr (Fin 1)) :=
  (List.range cs.size).foldl (fun total k ↦
    let c := cs.getD k 0
    if c = 0 then total else
    let term : Verified.Expr (Fin 1) := match k with
      | 0 => ratExpr c
      | 1 => if c = 1 then .var 0 else .mul (ratExpr c) (.var 0)
      | _ => if c = 1 then .pow (.var 0) k else .mul (ratExpr c) (.pow (.var 0) k)
    some (match total with
      | none => term
      | some t => .add t term)) none

/-- The particular solution `Re ∑ e ^ (λ x) g_λ (x)` as an expression. -/
def particular (a : Array ℚ) (f : ExpPoly) : Option (Verified.Expr (Fin 1)) := do
  -- Buckets `(a, |b|) ↦ (P_cos, P_sin)`.
  let mut buckets : List ((ℚ × ℚ) × (Array ℚ × Array ℚ)) := []
  for (l, P) in f do
    let g ← solveShifted a l P
    let b := l.im
    let key := (l.re, if b < 0 then -b else b)
    let cosPart := g.map (·.re)
    let sinPart := g.map fun z ↦ if b < 0 then z.im else -z.im
    let add (u v : Array ℚ) : Array ℚ :=
      (Array.range (max u.size v.size)).map fun k ↦ u.getD k 0 + v.getD k 0
    buckets := match buckets.find? (·.1 == key) with
      | some (_, (pc, ps)) =>
          buckets.filter (·.1 != key) ++ [(key, (add pc cosPart, add ps sinPart))]
      | none => buckets ++ [(key, (cosPart, sinPart))]
  let mut total : Option (Verified.Expr (Fin 1)) := none
  for ((ra, rb), (pc, ps)) in buckets do
    let trig : Option (Verified.Expr (Fin 1)) :=
      if rb = 0 then polyExpr pc
      else
        let c := (polyExpr pc).map fun term ↦ .mul term (.cos (linearExpr rb))
        let s := (polyExpr ps).map fun term ↦ .mul term (.sin (linearExpr rb))
        match c, s with
        | some c, some s => some (.add c s)
        | some c, none => some c
        | none, s => s
    let some body := trig | continue
    let term := if ra = 0 then body else .mul (.exp (linearExpr ra)) body
    total := some (match total with
      | none => term
      | some t => .add t term)
  return total.getD (.nat 0)

/-! ## Terms and statements -/

/-- The identifiers of a syntax tree. -/
partial def identifiers (stx : Syntax) : Array Name :=
  if stx.isIdent then #[stx.getId] else stx.getArgs.foldl (· ++ identifiers ·) #[]

/-- A rational as real term syntax. -/
def real {m : Type → Type} [Monad m] [MonadQuotation m] (q : ℚ) : m (TSyntax `term) := do
  `(($(← ratSyntax q) : ℝ))

/-- `a + b √m` as real term syntax, with the obvious simplifications. -/
def surd {m : Type → Type} [Monad m] [MonadQuotation m] (a b : ℚ) (n : Nat) :
    m (TSyntax `term) := do
  if n = 1 then return ← real (a + b)
  let root ← `(Real.sqrt $(⟨Syntax.mkNumLit (toString n)⟩))
  let magnitude := if b < 0 then -b else b
  let scaled ← if magnitude = 1 then pure root else `($(← real magnitude) * $root)
  if a = 0 then
    if b < 0 then `(-$scaled) else pure scaled
  else if b < 0 then `($(← real a) - $scaled) else `($(← real a) + $scaled)

/-- The right side of the solution formula `y x = …` in a statement. -/
partial def solutionRhs (e : Lean.Expr) : MetaM (Option String) := do
  match e.getAppFnArgs with
  | (``Iff, #[_, b]) => solutionRhs b
  | (``Exists, #[_, f]) => lambdaTelescope f fun _ body ↦ solutionRhs body
  | (``Eq, #[_, _, rhs]) => return some (← renderTerm rhs)
  | _ =>
      if e.isForall then forallTelescope e fun _ body ↦ solutionRhs body
      else return none

/-- The lemmas that restate evaluation in ordinary notation. -/
def cleanLemmas : List Name :=
  Series.seriesCleanLemmas ++ [``Matrix.cons_val_one, ``Matrix.cons_val_two,
    ``Matrix.cons_val_three, ``Matrix.head_cons, ``Matrix.tail_cons, ``sub_zero, ``zero_mul,
    ``mul_zero,
    ``Real.exp_zero, ``sub_eq_zero, ``neg_mul, ``Int.cast_neg, ``Int.cast_ofNat, ``neg_neg]

end CAS.Command.ExpPolynomials
