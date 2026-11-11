/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.Common
public import CAS.Command.RootIsolation
public import CAS.ExactTactic
public meta import CAS.Tactic.RouteRegistry

/-!
# Ranked simplification: `#cas [fullSimplify]`

`#cas [fullSimplify] e` collects several forms of `e`, ranks them by a complexity function, and
proves the simplest one equal to `e`. The candidates are the input itself, the outputs of the
checked simplification routes of the calculator (the configured side-conditioned pipeline, the
exact passes repeated until nothing changes or for at most six rounds, and the staged
factorization), the expanded and the factored forms of a polynomial with rational coefficients
(rational roots with their multiplicities and a remaining factor), the trigonometric expansion
of sines and cosines of sums and double angles followed by simplification, the expansion of
logarithms of products, quotients and powers followed by simplification, and the absolute value
for the square root of a perfect square.

The complexity functions are `leafCount` (the default), `depth` and `length` (the length of the
printed form); write `#cas [fullSimplify depth] e`. Ties go to the candidate with fewer
conditions, then to the shorter printed form. `#cas [expand] e`, `#cas [factor] e` and
`#cas [trigExpand] e` restrict the candidates to the expanded polynomial, the factored
polynomial and the trigonometric expansion, with the input as the candidate of last resort.

## Implementation notes

The search only proposes. We try the candidates in the order of their rank and report the first
whose identity `∀ x …, conditions → e = form` one of the closers proves; the kernel checks that
proof, so a wrong candidate costs time and nothing else. The closers are the rewrite that
produced the candidate (the trigonometric or logarithm lemmas, or `Real.sqrt_sq_eq_abs` for the
square root of a square), then `rfl`, `ring1`, the calculator's `cas` tactic, and `field_simp`
followed by `ring1`. The routes are those of `CAS/ClosedForm/Pipeline/Configured.lean` and
`CAS/ClosedForm/Pipeline/ExactRoutes.lean`; the rational roots of the factored forms come from
`rationalRoots` of `CAS/Command/RootIsolation.lean`, which factors no coefficient. With
`CASHex`, `#cas [factor]` first runs the backend of `CASHex/Factor.lean`, which factors into
irreducibles over `ℚ`, and falls back on the candidates here when that backend declines.

`leafCount` takes from Mathematica's `LeafCount` the count of the leaves of an expression tree
with each head as a leaf, and the weight three of a rational `p/q`, the leaves of the full form
`Rational[p, q]`. The other weights are ours: on our trees a sum, a difference, a product, a
quotient or a function such as a square root counts one plus its operands, and a negation `-a`
or a natural power `a ^ k` two plus `a`.

## References

* Wolfram Research, "LeafCount", Wolfram Language function, 1988 (updated 2022),
  <https://reference.wolfram.com/language/ref/LeafCount.html>.
-/

public meta section

namespace CAS.Command.FullSimplify

open Lean Elab Command Meta
open CAS.Command.InfoView
open CAS.Verified.Expr

/-! ## Expression forms -/

/-- A real expression in user coordinates, as displayed and stated. -/
inductive Form where
  | num (q : ℚ)
  | var (name : Name)
  | pi
  | e
  | add (a b : Form)
  | sub (a b : Form)
  | mul (a b : Form)
  | div (a b : Form)
  | neg (a : Form)
  | pow (a : Form) (k : Nat)
  | fn (name : String) (a : Form)
  | abs (a : Form)
  | rpow (a b : Form)
  deriving Inhabited, BEq

namespace Form

/-- Read a checked expression in the coordinates `names`. -/
partial def ofExpr {n : Nat} (names : List Name) : Verified.Expr (Fin n) → Form
  | .nat k => .num k
  | .int k => .num k
  | .rat p q => .num ((p : ℚ) / q)
  | .pi => .pi
  | .e => .e
  | .var i => .var (names.getD i.val `x)
  | .add a b => .add (ofExpr names a) (ofExpr names b)
  | .sub a b => .sub (ofExpr names a) (ofExpr names b)
  | .mul a b => .mul (ofExpr names a) (ofExpr names b)
  | .div a b => .div (ofExpr names a) (ofExpr names b)
  | .neg a => .neg (ofExpr names a)
  | .pow a k => .pow (ofExpr names a) k
  | .sin a => .fn "sin" (ofExpr names a)
  | .cos a => .fn "cos" (ofExpr names a)
  | .atan a => .fn "atan" (ofExpr names a)
  | .asin a => .fn "asin" (ofExpr names a)
  | .acos a => .fn "acos" (ofExpr names a)
  | .exp a => .fn "exp" (ofExpr names a)
  | .log a => .fn "log" (ofExpr names a)
  | .sqrt (.pow a 2) => .abs (ofExpr names a)
  | .sqrt a => .fn "sqrt" (ofExpr names a)
  | .rpow a b => .rpow (ofExpr names a) (ofExpr names b)

/-- The leaf count: one for an atom, and one plus the counts of its operands for an operation; a
non-integer rational counts three, and a negation or a natural power of `a` two plus the count of
`a`. -/
partial def leafCount : Form → Nat
  | .num q => if q.den = 1 then 1 else 3
  | .var _ | .pi | .e => 1
  | .add a b | .sub a b | .mul a b | .div a b | .rpow a b => 1 + leafCount a + leafCount b
  | .neg a => 2 + leafCount a
  | .pow a _ => 2 + leafCount a
  | .fn _ a | .abs a => 1 + leafCount a

/-- Nesting depth. -/
partial def depth : Form → Nat
  | .num _ | .var _ | .pi | .e => 1
  | .add a b | .sub a b | .mul a b | .div a b | .rpow a b => 1 + max (depth a) (depth b)
  | .neg a | .pow a _ | .fn _ a | .abs a => 1 + depth a

private def precedence : Form → Nat
  | .add _ _ | .sub _ _ => 1
  | .mul _ _ | .div _ _ => 2
  | .neg _ => 3
  | .pow _ _ | .rpow _ _ => 4
  | .num q => if q.den = 1 && 0 ≤ q then 5 else 2
  | _ => 5

/-- Printed form. -/
partial def render : Form → String
  | .num q => if q.den = 1 then toString q.num else s!"{q.num}/{q.den}"
  | .var name => renderName name
  | .pi => "pi"
  | .e => "e"
  | .add a b => s!"{render a} + {wrap 1 b}"
  | .sub a b => s!"{render a} - {wrap 2 b}"
  | .mul a b => s!"{wrap 2 a}*{wrap 3 b}"
  | .div a b => s!"{wrap 2 a}/{wrap 3 b}"
  | .neg a => s!"-{wrap 3 a}"
  | .pow a k => s!"{wrap 5 a}^{k}"
  | .rpow a b => s!"{wrap 5 a}^{wrap 5 b}"
  | .fn name a => s!"{name}({render a})"
  | .abs a => s!"|{render a}|"
where
  wrap (level : Nat) (form : Form) : String :=
    if precedence form < level then s!"({render form})" else render form

/-- Lean term syntax over real variables. -/
partial def toSyntax : Form → CommandElabM (TSyntax `term)
  | .num q => do
      let numerator : TSyntax `term := ⟨Syntax.mkNumLit (toString q.num.natAbs)⟩
      let magnitude ← if q.den = 1 then `(($numerator : ℝ)) else
        let denominator : TSyntax `term := ⟨Syntax.mkNumLit (toString q.den)⟩
        `(($numerator / $denominator : ℝ))
      if q.num < 0 then `(-$magnitude) else pure magnitude
  | .var name => pure (mkIdent name)
  | .pi => `(Real.pi)
  | .e => `(Real.exp 1)
  | .add a b => do `($(← toSyntax a) + $(← toSyntax b))
  | .sub a b => do `($(← toSyntax a) - $(← toSyntax b))
  | .mul a b => do `($(← toSyntax a) * $(← toSyntax b))
  | .div a b => do `($(← toSyntax a) / $(← toSyntax b))
  | .neg a => do `(-$(← toSyntax a))
  | .pow a k => do
      let exponent : TSyntax `term := ⟨Syntax.mkNumLit (toString k)⟩
      `($(← toSyntax a) ^ ($exponent : ℕ))
  | .rpow a b => do `($(← toSyntax a) ^ ($(← toSyntax b) : ℝ))
  | .abs a => do `(|$(← toSyntax a)|)
  | .fn name a => do
      let argument ← toSyntax a
      match name with
      | "sin" => `(Real.sin $argument)
      | "cos" => `(Real.cos $argument)
      | "atan" => `(Real.arctan $argument)
      | "asin" => `(Real.arcsin $argument)
      | "acos" => `(Real.arccos $argument)
      | "exp" => `(Real.exp $argument)
      | "log" => `(Real.log $argument)
      | _ => `(Real.sqrt $argument)

/-- One bottom-up step of display cleanup: repeated factors become powers, sums with negated
terms become differences, and units disappear. -/
partial def tidyStep : Form → Form
  | .add a b =>
      match tidyStep a, tidyStep b with
      | a, .num 0 => a
      | .num 0, b => b
      | a, .neg b => .sub a b
      | a, .num q => if q < 0 then .sub a (.num (-q)) else .add a (.num q)
      | a, .mul (.num q) b =>
          if q = -1 then .sub a b else if q < 0 then .sub a (.mul (.num (-q)) b)
          else .add a (.mul (.num q) b)
      | a, b => .add a b
  | .sub a b =>
      match tidyStep a, tidyStep b with
      | a, .num 0 => a
      | a, .neg b => .add a b
      | a, b => .sub a b
  | .mul a b =>
      match tidyStep a, tidyStep b with
      | .num 1, b => b
      | a, .num 1 => a
      | .num q, b => if q = -1 then .neg b else .mul (.num q) b
      | .pow a k, b => if a == b then .pow a (k + 1) else .mul (.pow a k) b
      | a, .pow b k => if a == b then .pow a (k + 1) else .mul a (.pow b k)
      | a, b => if a == b then .pow a 2 else .mul a b
  | .neg a =>
      match tidyStep a with
      | .neg a => a
      | .num q => .num (-q)
      | a => .neg a
  | .div a b => .div (tidyStep a) (tidyStep b)
  | .pow a k =>
      match tidyStep a with
      | .pow a j => .pow a (j * k)
      | a => if k = 1 then a else .pow a k
  | .rpow a b => .rpow (tidyStep a) (tidyStep b)
  | .fn name a => .fn name (tidyStep a)
  | .abs a => .abs (tidyStep a)
  | form => form

/-- Display cleanup to a fixed point, at most eight rounds. -/
def tidy (form : Form) : Form := Id.run do
  let mut current := form
  for _ in [0:8] do
    let next := tidyStep current
    if next == current then break
    current := next
  return current

end Form

/-- A side condition of a candidate. -/
inductive Condition where
  | nonzero (a : Form)
  | positive (a : Form)
  deriving BEq

namespace Condition

/-- Printed form, `a ≠ 0` or `a > 0`. -/
def render : Condition → String
  | .nonzero a => s!"{a.render} ≠ 0"
  | .positive a => s!"{a.render} > 0"

/-- Lean term syntax, `a ≠ 0` or `0 < a`. -/
def toSyntax : Condition → CommandElabM (TSyntax `term)
  | .nonzero a => do `($(← a.toSyntax) ≠ 0)
  | .positive a => do `(0 < $(← a.toSyntax))

end Condition

/-- The complexity functions. -/
inductive Complexity where
  | leafCount | depth | length
  deriving BEq

/-- The cost of a form: its leaf count, its depth, or the length of its printed form. -/
def Complexity.cost : Complexity → Form → Nat
  | .leafCount, f => f.leafCount
  | .depth, f => f.depth
  | .length, f => f.render.length

/-- The name of the complexity function, as in `#cas [fullSimplify depth] e`. -/
def Complexity.label : Complexity → String
  | .leafCount => "leafCount"
  | .depth => "depth"
  | .length => "length"

/-- A proposed form with its conditions, its origin and an optional dedicated proof. -/
structure Candidate where
  /-- The proposed form of the input. -/
  form : Form
  /-- The side conditions under which the input equals `form`. -/
  conditions : List Condition := []
  /-- The route that produced the form, such as `"factored polynomial"`, as reported. -/
  origin : String
  /-- A tactic tried first on `∀ x …, conditions → e = form`, after the introductions. -/
  closer? : Option (TSyntax `tactic) := none

/-! ## Polynomial forms -/

/-- Coefficients of a univariate polynomial, lowest degree first, without trailing zeros. -/
def trimCoefficients (cs : List ℚ) : List ℚ :=
  (cs.reverse.dropWhile (· == 0)).reverse

/-- Evaluate a coefficient list. -/
def evalCoefficients (cs : List ℚ) (x : ℚ) : ℚ :=
  cs.foldr (fun c total ↦ c + x * total) 0

/-- The rational roots with multiplicities, and the remaining factor: the exact quotient, which
keeps the leading coefficient of `cs`. The roots come from `RootIsolation.rationalRoots`, which
reads each one off a narrow isolating interval of the square-free part, so no coefficient is
factored and the size of the coefficients is not bounded. This search is in the core library,
although Hex factors completely, for the commands that use it without Hex: `#cas [factor]` splits
off rational roots with it, so that `#cas [factor] (x^4 - 5*x^2 + 4)` works without Hex, and bare
`cas`'s command route, `dsolve`, `sum`, `rsolve` and `eigenvalues` call it too. -/
def rationalRoots (cs : List ℚ) : List (ℚ × Nat) × List ℚ :=
  let (roots, rest, _) := CAS.Command.RootIsolation.rationalRoots cs
  (roots, rest)

/-- The form of `∑ c_k x ^ k`, highest degree first. -/
def polynomialForm (x : Form) (cs : List ℚ) : Form := Id.run do
  let monomial (c : ℚ) (k : Nat) : Form :=
    let power := match k with
      | 0 => Form.num 1
      | 1 => x
      | _ => .pow x k
    if k = 0 then .num c
    else if c = 1 then power
    else .mul (.num c) power
  let terms := ((cs.zipIdx).filter (·.1 != 0)).reverse
  match terms with
  | [] => return .num 0
  | (c, k) :: rest =>
      let mut total := if c < 0 && k > 0 then .neg (monomial (-c) k) else monomial c k
      for (c, k) in rest do
        total := if c < 0 then .sub total (monomial (-c) k) else .add total (monomial c k)
      return total

/-- How the factors of a univariate factorization are written: the linear factor of a root
`a / b` (with `b > 0`), the polynomial with given coefficients, and the extra factor of a
missing top degree (used by homogeneous polynomials). -/
structure Writer where
  /-- The linear factor of a rational root `a / b`, with `b > 0`. -/
  linear : ℚ → Form
  /-- The polynomial with the given coefficients, lowest degree first. -/
  polynomial : List ℚ → Form
  /-- The factor of `k` missing top degrees (`y ^ k` for the homogeneous writer), or
  `none`. -/
  topFactor : Nat → Option Form := fun _ ↦ none

/-- The univariate writer in the variable `x`. -/
def univariateWriter (x : Form) : Writer where
  linear r :=
    if r = 0 then x
    else
      let leadingTerm := if r.den = 1 then x else .mul (.num r.den) x
      if r < 0 then .add leadingTerm (.num (-r * r.den))
      else .sub leadingTerm (.num (r * r.den))
  polynomial cs := polynomialForm x cs

/-- The homogeneous writer in `x` and `y`: the root `a / b` of the dehomogenized polynomial in
`x / y` is the factor `b x - a y`. -/
def homogeneousWriter (x y : Form) : Writer where
  linear r :=
    if r = 0 then x
    else
      let leadingTerm := if r.den = 1 then x else .mul (.num r.den) x
      let a := if r < 0 then -r * r.den else r * r.den
      let other := if a = 1 then y else .mul (.num a) y
      if r < 0 then .add leadingTerm other else .sub leadingTerm other
  polynomial cs :=
    let degree := cs.length - 1
    let terms := ((cs.zipIdx).filter (·.1 != 0)).reverse.map fun (c, k) ↦
      let factors : List Form :=
        (if k = 0 then [] else [if k = 1 then x else .pow x k]) ++
          (if degree - k = 0 then [] else [if degree - k = 1 then y else .pow y (degree - k)])
      let monomial := match factors with
        | [] => Form.num 1
        | first :: rest => rest.foldl .mul first
      (c, if factors.isEmpty then Form.num c else if c = 1 then monomial
        else if c = -1 then .neg monomial else .mul (.num c) monomial)
    match terms with
    | [] => .num 0
    | (_, first) :: rest => rest.foldl (fun total (c, t) ↦
        match t with
        | .mul (.num q) m => if c < 0 then .sub total (.mul (.num (-q)) m) else .add total t
        | .neg m => .sub total m
        | _ => .add total t) first
  topFactor k := if k = 0 then none else some (if k = 1 then y else .pow y k)

/-- The factored form `C ∏ (b x - a) ^ m · q (x)` of a polynomial through its rational roots;
`degree` is the homogeneous degree when larger than the length of `cs`. -/
def factoredWith (writer : Writer) (cs : List ℚ) (degree : Nat) : Option Form := Id.run do
  let cs := trimCoefficients cs
  if cs.length ≤ 1 then return none
  let missing := degree + 1 - cs.length
  let (roots, rest) := rationalRoots cs
  if roots.isEmpty && missing = 0 then return none
  if roots.isEmpty && cs.length = 2 then return none
  -- Scale the remaining factor to a primitive integer polynomial with positive leading term.
  let restScale := rest.foldl (fun l c ↦ Nat.lcm l c.den) 1
  let restIntegers := rest.map fun c ↦ c * (restScale : ℚ)
  let restContent := restIntegers.foldl (fun g c ↦ Nat.gcd g c.num.natAbs) 0
  let restLeading := restIntegers.getLastD 1
  let sign : ℚ := if restLeading < 0 then -1 else 1
  let primitive := restIntegers.map fun c ↦ c * sign / (restContent : ℚ)
  let mut constant : ℚ := sign * restContent / restScale
  let mut factors : List Form := []
  for (r, m) in roots do
    let linear := writer.linear r
    constant := constant / (r.den : ℚ) ^ m
    factors := factors ++ [if m = 1 then linear else .pow linear m]
  -- A missing top degree is a power of the second variable, written after the power of `x`.
  if let some top := writer.topFactor missing then
    let position := if roots.head?.map (·.1) == some 0 then 1 else 0
    factors := factors.take position ++ [top] ++ factors.drop position
  if primitive.length > 1 then
    factors := factors ++ [writer.polynomial primitive]
  let some first := factors.head? | return none
  let product := factors.tail.foldl .mul first
  if constant = 1 then return some product
  if constant = -1 then return some (.neg product)
  return some (.mul (.num constant) product)

/-- The factored form of a univariate polynomial. -/
def factoredForm (x : Form) (cs : List ℚ) : Option Form :=
  factoredWith (univariateWriter x) cs (trimCoefficients cs).length.pred

/-- The natural `g`-th root of `a`, when it is exact. -/
def natRoot? (a g : Nat) : Option Nat := Id.run do
  if g = 0 then return none
  let mut lo := 0
  let mut hi := a + 1
  while lo + 1 < hi do
    let mid := (lo + hi) / 2
    if mid ^ g ≤ a then lo := mid else hi := mid
  return if lo ^ g = a then some lo else none

/-- A rational `g`-th root, when it is exact. -/
def ratRoot? (q : ℚ) (g : Nat) : Option ℚ := do
  let numerator ← natRoot? q.num.natAbs g
  let denominator ← natRoot? q.den g
  let root : ℚ := (numerator : ℚ) / denominator
  if q < 0 then
    if g % 2 = 1 then return -root else none
  else return root

/-- Multiply a coefficient list by `x - r`. -/
def mulLinear (cs : List ℚ) (r : ℚ) : List ℚ :=
  (List.range (cs.length + 1)).map fun k ↦
    (if k = 0 then 0 else cs.getD (k - 1) 0) - r * cs.getD k 0

/-- `p = s ^ g` for a polynomial `s` with rational roots, when the roots of `p` split completely
with multiplicities divisible by `g ≥ 2` and the leading coefficient is a `g`-th power. -/
def perfectPower? (cs : List ℚ) : Option (List ℚ × Nat) := Id.run do
  let cs := trimCoefficients cs
  let (roots, rest) := rationalRoots cs
  if rest.length != 1 || roots.isEmpty then return none
  let g := roots.foldl (fun g (_, m) ↦ Nat.gcd g m) 0
  if g < 2 then return none
  let some leading := ratRoot? (rest.getD 0 0) g | return none
  let mut base : List ℚ := [leading]
  for (r, m) in roots do
    for _ in [0:m / g] do
      base := mulLinear base r
  return some (base, g)

/-- The univariate coefficient list of a polynomial in coordinate `i`, if no other coordinate
occurs. -/
def univariateCoefficients {n : Nat} (p : Verified.Expr.Alg.MvPoly n) (i : Fin n) :
    Option (List ℚ) := do
  for (_, monomial) in p do
    for j in List.finRange n do
      if j != i && monomial j != 0 then none
  let degree := p.foldl (fun d (_, monomial) ↦ max d (monomial i)) 0
  return (List.range (degree + 1)).map fun k ↦
    p.foldl (fun sum (c, monomial) ↦ if monomial i = k then sum + c else sum) 0

/-- For a homogeneous polynomial of degree `d` in the coordinates `i` and `j` only, the
coefficients of `x ^ k y ^ (d - k)`, lowest `k` first, and `d`. -/
def homogeneousCoefficients {n : Nat} (p : Verified.Expr.Alg.MvPoly n) (i j : Fin n) :
    Option (List ℚ × Nat) := do
  let terms := p.filter (·.1 != 0)
  let (_, first) ← terms.head?
  let d := first i + first j
  for (_, monomial) in terms do
    for k in List.finRange n do
      if k != i && k != j && monomial k != 0 then none
    if monomial i + monomial j != d then none
  if d < 2 then none
  return ((List.range (d + 1)).map fun k ↦
    terms.foldl (fun sum (c, monomial) ↦ if monomial i = k then sum + c else sum) 0, d)

/-- The sum of the monomials of a canonical multivariate polynomial (as `mvPolyOf?` returns it),
in descending graded lexicographic order. -/
def multivariateForm {n : Nat} (names : List Name) (p : Verified.Expr.Alg.MvPoly n) : Form :=
  Id.run do
  let factors (monomial : Fin n → Nat) : List Form :=
    (List.finRange n).filterMap fun i ↦
      let k := monomial i
      let x : Form := .var (names.getD i.val `x)
      if k = 0 then none else some (if k = 1 then x else .pow x k)
  -- `c x₁ ^ k₁ ⋯` as a left-nested product starting with the coefficient.
  let term (c : ℚ) (monomial : Fin n → Nat) : Form :=
    match factors monomial with
    | [] => .num c
    | first :: rest =>
        let start : Form := if c = 1 then first else .mul (.num c) first
        rest.foldl .mul start
  match p with
  | [] => return .num 0
  | (c, m) :: rest =>
      let mut total :=
        if c < 0 && !(factors m).isEmpty then .neg (term (-c) m) else term c m
      for (c, m) in rest do
        total := if c < 0 then .sub total (term (-c) m) else .add total (term c m)
      return total

/-- The displayed form of a condition expression: its expanded polynomial when it is one. -/
def conditionForm {n : Nat} (names : List Name) (a : Verified.Expr (Fin n)) : Form :=
  match Verified.Expr.Alg.mvPolyOf? (Verified.Expr.simplify a) with
  | some p => multivariateForm names p
  | none => Form.ofExpr names a

/-- Read a nonzero requirement of a simplification route; `sqrt a` encodes `0 < a`. -/
def Condition.ofRequirement {n : Nat} (names : List Name) :
    Verified.Expr (Fin n) → Condition
  | .sqrt a => .positive (conditionForm names a)
  | a => .nonzero (conditionForm names a)

/-! ## Trigonometric and logarithmic expansion -/

/-- Expand sines and cosines of sums, differences and double angles. -/
partial def trigExpand {ι : Type*} : Verified.Expr ι → Verified.Expr ι
  | .sin (.mul (.nat 2) a) =>
      let a := trigExpand a
      .mul (.mul (.nat 2) (.sin a)) (.cos a)
  | .cos (.mul (.nat 2) a) =>
      let a := trigExpand a
      .sub (.pow (.cos a) 2) (.pow (.sin a) 2)
  | .sin (.add a b) =>
      let a := trigExpand a
      let b := trigExpand b
      .add (.mul (.sin a) (.cos b)) (.mul (.cos a) (.sin b))
  | .cos (.add a b) =>
      let a := trigExpand a
      let b := trigExpand b
      .sub (.mul (.cos a) (.cos b)) (.mul (.sin a) (.sin b))
  | .sin (.sub a b) =>
      let a := trigExpand a
      let b := trigExpand b
      .sub (.mul (.sin a) (.cos b)) (.mul (.cos a) (.sin b))
  | .cos (.sub a b) =>
      let a := trigExpand a
      let b := trigExpand b
      .add (.mul (.cos a) (.cos b)) (.mul (.sin a) (.sin b))
  | .add a b => .add (trigExpand a) (trigExpand b)
  | .sub a b => .sub (trigExpand a) (trigExpand b)
  | .mul a b => .mul (trigExpand a) (trigExpand b)
  | .div a b => .div (trigExpand a) (trigExpand b)
  | .neg a => .neg (trigExpand a)
  | .pow a k => .pow (trigExpand a) k
  | .sin a => .sin (trigExpand a)
  | .cos a => .cos (trigExpand a)
  | .exp a => .exp (trigExpand a)
  | .log a => .log (trigExpand a)
  | .sqrt a => .sqrt (trigExpand a)
  | expression => expression

/-- Expand logarithms of products, quotients and natural powers, collecting the nonzero
conditions of `Real.log_mul` and `Real.log_div`. -/
partial def logExpand {ι : Type*} :
    Verified.Expr ι → Verified.Expr ι × List (Verified.Expr ι)
  | .log (.mul a b) =>
      let (a', ca) := logExpand (.log a)
      let (b', cb) := logExpand (.log b)
      (.add a' b', [a, b] ++ ca ++ cb)
  | .log (.div a b) =>
      let (a', ca) := logExpand (.log a)
      let (b', cb) := logExpand (.log b)
      (.sub a' b', [a, b] ++ ca ++ cb)
  | .log (.pow a k) =>
      let (a', ca) := logExpand (.log a)
      (.mul (.nat k) a', ca)
  | .add a b =>
      let (a', ca) := logExpand a
      let (b', cb) := logExpand b
      (.add a' b', ca ++ cb)
  | .sub a b =>
      let (a', ca) := logExpand a
      let (b', cb) := logExpand b
      (.sub a' b', ca ++ cb)
  | .mul a b =>
      let (a', ca) := logExpand a
      let (b', cb) := logExpand b
      (.mul a' b', ca ++ cb)
  | .neg a =>
      let (a', ca) := logExpand a
      (.neg a', ca)
  | expression => (expression, [])

/-! ## Candidates -/

/-- Which candidates a mode collects. -/
inductive Mode where
  | full | expand | factor | trigExpand
  deriving BEq

/-- The command name of the mode, as in `#cas [expand] e`. -/
def Mode.label : Mode → String
  | .full => "fullSimplify"
  | .expand => "expand"
  | .factor => "factor"
  | .trigExpand => "trigExpand"

/-- The candidates of `mode` for the reified input. -/
def candidates (mode : Mode) (reified : ReifiedExpr) : CommandElabM (List Candidate) := do
  let names := reified.names
  let input := reified.expr
  let ofExpr := Form.ofExpr names
  let route (name : String) (r : SideClaimRoute (Fin names.length)) : Candidate :=
    { form := ofExpr r.rhs
      conditions := (r.nonzero.map (Condition.ofRequirement names)).eraseDups
      origin := name }
  let mut out : List Candidate := [{ form := ofExpr input, origin := "input" }]
  if mode == .full then
    out := out ++ [route "configured simplification" (simplifyFinSideClaimRoute input),
      route "exact passes" (checkedClaimRoute 6 input),
      route "staged factorization" (factorClaimRoute input)]
  -- Polynomial forms.
  if mode == .full || mode == .expand || mode == .factor then
    if let some p := Verified.Expr.Alg.mvPolyOf? (Verified.Expr.simplify input) then
      if mode != .factor then
        out := out ++ [{ form := multivariateForm names p, origin := "expanded polynomial" }]
      for i in List.finRange names.length do
        if let some cs := univariateCoefficients p i then
          let x : Form := .var (names.getD i.val `x)
          if mode != .factor then
            out := out ++ [{ form := polynomialForm x cs, origin := "expanded polynomial" }]
          if mode != .expand then
            if let some f := factoredForm x cs then
              out := out ++ [{ form := f, origin := "factored polynomial" }]
            if let some (base, g) := perfectPower? cs then
              out := out ++ [{ form := .pow (polynomialForm x base) g, origin := "perfect power" }]
              if let some f := factoredForm x base then
                out := out ++ [{ form := .pow f g, origin := "perfect power" }]
      -- Homogeneous polynomials in two variables, through `x / y`.
      if mode != .expand then
        for i in List.finRange names.length do
          for j in List.finRange names.length do
            if i == j then continue
            if let some (cs, d) := homogeneousCoefficients p i j then
              let x : Form := .var (names.getD i.val `x)
              let y : Form := .var (names.getD j.val `y)
              if let some f := factoredWith (homogeneousWriter x y) cs d then
                out := out ++ [{ form := f, origin := "factored homogeneous polynomial" }]
              if let some (base, g) := perfectPower? cs then
                if base.length = d / g + 1 then
                  let inner := (homogeneousWriter x y).polynomial base
                  out := out ++ [{ form := .pow inner g, origin := "perfect power" }]
  -- Trigonometric expansion followed by simplification.
  if mode == .full || mode == .trigExpand then
    let expanded := trigExpand input
    if expanded != input then
      let tactic ← `(tactic| (simp only [Real.sin_two_mul, Real.cos_two_mul, Real.sin_add,
          Real.cos_add, Real.sin_sub, Real.cos_sub] at * <;> first | ring1 | cas))
      out := out ++ [Candidate.mk (ofExpr expanded) [] "trigonometric expansion" (some tactic)]
      if mode == .full then
        let r := simplifyFinSideClaimRoute expanded
        let c := route "trigonometric expansion and simplification" r
        out := out ++ [Candidate.mk c.form c.conditions c.origin (some tactic)]
  -- Logarithm expansion followed by simplification.
  if mode == .full then
    let (expanded, conditions) := logExpand input
    if expanded != input then
      let r := simplifyFinSideClaimRoute expanded
      let tactic ← `(tactic| (simp only [Real.log_mul, Real.log_div, Real.log_pow, ne_eq,
          not_false_eq_true, *] <;> first | ring1 | cas))
      let logConditions := ((conditions.map (Condition.ofRequirement names)) ++
          r.nonzero.map (Condition.ofRequirement names)).eraseDups
      out := out ++ [Candidate.mk (ofExpr r.rhs) logConditions
        "logarithm expansion and simplification" (some tactic)]
  -- Square root of a perfect square.
  if mode == .full then
    if let .sqrt argument := input then
      if let some p := Verified.Expr.Alg.mvPolyOf? (Verified.Expr.simplify argument) then
        for i in List.finRange names.length do
          if let some cs := univariateCoefficients p i then
            let (roots, rest) := rationalRoots cs
            let leading := rest.getLastD 0
            let numerator := Nat.sqrt leading.num.natAbs
            let denominator := Nat.sqrt leading.den
            if rest.length = 1 && 0 < leading && numerator * numerator = leading.num.natAbs &&
                denominator * denominator = leading.den && !roots.isEmpty &&
                roots.all (fun (_, m) ↦ m % 2 == 0) then
              let x : Form := .var (names.getD i.val `x)
              let half := roots.map fun (r, m) ↦ (r, m / 2)
              let base := half.foldl (fun (acc : List ℚ) (r, m) ↦ Id.run do
                let mut acc := acc
                for _ in [0:m] do
                  -- Multiply `acc` by `x - r`.
                  acc := (List.range (acc.length + 1)).map fun k ↦
                    (if k = 0 then 0 else acc.getD (k - 1) 0) - r * acc.getD k 0
                return acc) [(numerator : ℚ) / denominator]
              let factored := (factoredForm x base).getD (polynomialForm x base)
              let factoredSyntax ← factored.toSyntax
              let argumentSyntax ← (ofExpr argument).toSyntax
              let tactic ← `(tactic| rw [show $argumentSyntax = ($factoredSyntax) ^ (2 : ℕ) by ring,
                  Real.sqrt_sq_eq_abs])
              out := out ++
                [Candidate.mk (.abs factored) [] "square root of a square" (some tactic)]
  -- Display cleanup of the computed forms. Square-root candidates keep their exact form.
  return out.map fun c ↦
    if c.origin == "input" || c.origin == "square root of a square" then c
    else { c with form := c.form.tidy }

/-! ## Ranking and proof -/

/-- Try to prove `∀ x …, conditions → lhs = form` for a candidate. The statement is elaborated
once and the closers are tried on it in turn. -/
def proveCandidate (names : List Name) (lhs : Form) (candidate : Candidate) :
    CommandElabM (Option (Lean.Expr × Lean.Expr)) := do
  let lhsSyntax ← lhs.toSyntax
  let rhsSyntax ← candidate.form.toSyntax
  let mut body ← `($lhsSyntax = $rhsSyntax)
  for condition in candidate.conditions.reverse do
    body ← `($(← condition.toSyntax) → $body)
  let binders := names.toArray.map mkIdent
  let statement ← if binders.isEmpty then pure body else `(∀ $binders* : ℝ, $body)
  let hypotheses := (List.range candidate.conditions.length).toArray.map fun i ↦
    mkIdent (Name.mkSimple s!"h{i}")
  let introduce ← `(tactic| intro $(binders ++ hypotheses)*)
  let closers : List (TSyntax `tactic) := (candidate.closer?.toList) ++
    [← `(tactic| rfl), ← `(tactic| ring1), ← `(tactic| cas),
      ← `(tactic| (field_simp; ring1))]
  -- A closed proposition without metavariables, so each attempt below can use it.
  let some proposition ← liftTermElabM do
      let saved ← saveState
      try
        let proposition ← Term.withoutErrToSorry <| Term.elabTerm statement none
        Term.synthesizeSyntheticMVarsNoPostponing
        let proposition ← instantiateMVars proposition
        if proposition.hasSyntheticSorry || proposition.hasMVar then
          saved.restore
          return none
        return some proposition
      catch _ =>
        saved.restore
        return none
    | return none
  for closer in closers do
    let attempt ← liftTermElabM do
      let saved ← saveState
      try
        let proofSyntax ← if binders.isEmpty && hypotheses.isEmpty then `(by $closer:tactic)
          else `(by $introduce:tactic; $closer:tactic)
        let proof ← Term.withoutErrToSorry <|
          Term.elabTerm proofSyntax (some proposition)
        Term.synthesizeSyntheticMVarsNoPostponing
        let proof ← instantiateMVars proof
        if proof.hasSyntheticSorry || proof.hasMVar then
          saved.restore
          return none
        return some (proposition, proof)
      catch _ =>
        saved.restore
        return none
    if attempt.isSome then return attempt
  return none

/-- Run a ranked simplification mode. -/
def logRanked (ref : Syntax) (mode : Mode) (complexity : Complexity) (input : Syntax) :
    CommandElabM Unit := do
  let reified ← parseInferred input
  let all ← candidates mode reified
  let lhs := Form.ofExpr reified.names reified.expr
  -- Remove duplicates and rank.
  let mut unique : Array Candidate := #[]
  for candidate in all do
    unless unique.any (fun c ↦ c.form == candidate.form &&
        c.conditions.length ≤ candidate.conditions.length) do
      unique := unique.push candidate
  -- The candidate's position breaks ties, so equally ranked candidates keep their order.
  let key (entry : Candidate × Nat) : List Nat :=
    [complexity.cost entry.1.form, entry.1.conditions.length, entry.1.form.render.length, entry.2]
  let ranked := (unique.zipIdx.qsort fun a b ↦ key a < key b).map (·.1)
  -- In the restricted modes the input is a candidate of last resort.
  let ranked := if mode == .full then ranked else
    ranked.filter (·.origin != "input") ++ ranked.filter (·.origin == "input")
  let mut chosen : Option (Candidate × Lean.Expr × Lean.Expr) := none
  for candidate in ranked do
    if chosen.isSome then break
    if let some (proposition, proof) ← proveCandidate reified.names lhs candidate then
      chosen := some (candidate, proposition, proof)
  let some (best, _, proof) := chosen
    | throwErrorAt input "{mode.label}: no candidate could be proved"
  let report ← liftTermElabM do
    evidenceReportMessage #[← CAS.Tactic.Explanation.UncheckedExplanationStep.ofProof
      s!"Identity with the {best.origin}" proof]
  let table := ranked.toList.map fun c ↦
    m!"{c.origin}: {c.form.render}  [{complexity.label} {complexity.cost c.form}, \
      conditions {c.conditions.length}]"
  logReport ref {
    domain := renderRealDomain reified.names
    input := reified.render
    inputType := "scalar ℝ"
    output := best.form.render
    outputType := "scalar ℝ"
    conditions? := if best.conditions.isEmpty then none else
      some ("; ".intercalate (best.conditions.map Condition.render))
  } #[
    computationNode "Ranked candidates (proposals, not proof)" table.toArray,
    report
  ]

end CAS.Command.FullSimplify

namespace CAS.Command

open Lean Elab Command

/-- `#cas [fullSimplify] e` searches checked forms of the real expression `e` and prints the
simplest one under a complexity function, with the conditions under which it equals `e`.

## Theorem
For the variables `x₁, …, xₙ` of `e` and the printed form `e'`, the report proves
`∀ x₁ … xₙ : ℝ, c₁ → … → cₖ → e = e'` about Mathlib's real functions, where `c₁, …, cₖ` are the
printed conditions. The proof is `ring`, `cas`, `field_simp` and `ring`, or the trigonometric,
logarithm or square-root rewrite that produced the form.

## Conditions and limits
The candidates are the input, the results of the checked simplification routes, the expanded and
the factored polynomial, the trigonometric expansion, the expansion of logarithms of products,
quotients and powers, and `|t|` for the square root of a perfect square `t ^ 2`. The reported
form is the simplest candidate whose identity the kernel accepts; ties go to the candidate with
fewer conditions. The variables and functions are those of `#cas [simplify]`.

## Options
An optional complexity function after the mode name: `leafCount` (the default: the number of
atoms and operations, with a power counting its exponent), `depth` (the depth of the expression
tree) or `length` (the length of the printed form), as in `#cas [fullSimplify depth] e`.

## Examples
```lean
#cas [fullSimplify] (x^5 + 5*x^4 + 10*x^3 + 10*x^2 + 5*x + 1)
```
```output
Output (scalar ℝ): (x + 1)^5
```
```lean
#cas [fullSimplify] (log (x*y) - log x - log y)
```
```output
Output (scalar ℝ): 0
Conditions: x ≠ 0; y ≠ 0
```
```lean
#cas [fullSimplify] (sqrt (x^2 + 2*x + 1))
```
```output
Output (scalar ℝ): |x + 1|
```

## In a proof
```lean
theorem fullSimplify_log (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    Real.log (x * y) - Real.log x - Real.log y = 0 := by
  cas
```

## See also
Mathematica `FullSimplify` and `LeafCount`, SymPy `simplify` with a `measure`. The modes
`simplify`, `expand`, `factor` and `trigExpand`.

## Possible issues
```lean
#cas [fullSimplify size] (x + 1)
```
```output
unknown complexity function size; use leafCount, depth or length
```
Use one of the three complexity functions.

The tactic `cas` does not prove an identity with a square root, such as
`Real.sqrt (x ^ 2 + 2 * x + 1) = |x + 1|`, without sign hypotheses; its error message lists the
candidate conditions (here `0 ≤ x ^ 2 + 2 * x + 1`) to put in the local context.
-/
syntax (name := casFullSimplifyCommand) "#cas" "[" &"fullSimplify" (ident)? "]" term : command

/-- `#cas [expand] e` multiplies out the products and natural powers of the polynomial `e`.

## Theorem
For the variables `x₁, …, xₙ` of `e` and the printed expansion `p`, the report proves
`∀ x₁ … xₙ : ℝ, e = p` about Mathlib's real numbers, by `ring`. For a call of a family of
polynomials, such as `ChebyshevT 5 x`, it proves the expansion of Mathlib's polynomial, as
`#cas (ChebyshevT 5 x)` does.

## Conditions and limits
The input is a polynomial with rational coefficients in real variables, or a call
`ChebyshevT n x`, `ChebyshevU n x`, `HermiteH n x`, `HermiteHe n x`, `LegendreP n x` or
`BernoulliB n x`. An expression that is not a polynomial, such as `sin (x + y)` or
`1 / (x + 1) ^ 2`, is printed unchanged.

## Options
None.

## Examples
```lean
#cas [expand] ((x + 1)^3 * (y - 2))
```
```output
Output (scalar ℝ): x^3*y - 2*x^3 + 3*x^2*y - 6*x^2 + 3*x*y - 6*x + y - 2
```
```lean
#cas [expand] ((a + b)^4)
```
```output
Output (scalar ℝ): a^4 + 4*a^3*b + 6*a^2*b^2 + 4*a*b^3 + b^4
```
```lean
#cas [expand] ((x - 1/2)^2 * (x + 2))
```
```output
Output (scalar ℝ): x^3 + x^2 - 7/4*x + 1/2
```

## In a proof
```lean
theorem expand_product (x y : ℝ) :
    (x + 1) ^ 3 * (y - 2) =
      x ^ 3 * y - 2 * x ^ 3 + 3 * x ^ 2 * y - 6 * x ^ 2 + 3 * x * y - 6 * x + y - 2 := by
  cas
```

## See also
Mathematica `Expand`, SymPy `expand`. The modes `factor`, `collect`, `trigExpand` and
`fullSimplify`, and the calls of the families of polynomials, such as `ChebyshevT n x`.

## Possible issues
```lean
#cas [expand] (sin (x + y))
```
```output
Output (scalar ℝ): sin(x + y)
```
The argument of a function is not expanded; `#cas [trigExpand]` expands sines and cosines of sums.
```lean
#cas [expand] (1 / (x + 1) ^ 2)
```
```output
Output (scalar ℝ): 1/(x + 1)^2
```
A quotient is left as it is; `#cas [together]` and `#cas [apart]` rewrite rational functions.
-/
syntax (name := casExpandCommand) "#cas" "[" &"expand" "]" term : command

/-- `#cas [factor] p` factors the polynomial `p` with rational coefficients into a product of
polynomials.

## Theorem
For the variables `x₁, …, xₙ` of `p` and the printed product `q`, the report proves
`∀ x₁ … xₙ : ℝ, p = q` about Mathlib's real numbers, by `ring`.

## Conditions and limits
The input is a polynomial with rational coefficients. Without Hex, the factors come from the
rational roots with their multiplicities, from perfect powers, and from homogeneous polynomials in
two variables; a remaining factor of degree two or more is printed whole and is not claimed to be
irreducible. With `CASHex.Factor` imported (built by `lake -R -Khex=on build CASHex`), the
factors are irreducible over `ℚ` whenever Hex certifies every one of them.

## Options
None.

## Examples
```lean
#cas [factor] (2*x^3 - 3*x^2 + 1)
```
```output
Output (scalar ℝ): (x - 1)^2*(2*x + 1)
```
```lean
#cas [factor] (x^3*y - x*y^3)
```
```output
Output (scalar ℝ): x*y*(x - y)*(x + y)
```
```lean
#cas [factor] (x^6 - 1)
```
```output
Output (scalar ℝ): (x - 1)*(x + 1)*(x^4 + x^2 + 1)
```

## In a proof
```lean
theorem factor_cubic (x : ℝ) : 2 * x ^ 3 - 3 * x ^ 2 + 1 = (x - 1) ^ 2 * (2 * x + 1) := by
  cas
```

## See also
Mathematica `Factor`, SymPy `factor`, Hex `Hex.ZPoly.factorize` (through `CASHex.Factor`). The
modes `expand`, `apart`, `roots` and `solve`. Oracle route: `#cas [factor, oracle := sympy] p`.

## Possible issues
```lean
#cas [factor] (x^4 + 4)
```
```output
Output (scalar ℝ): x^4 + 4
```
Without Hex, a polynomial with no rational root and no perfect-power or homogeneous form stays
whole. With `CASHex.Factor` imported the output is
`Output (scalar ℝ, factors irreducible over ℚ): (x^2 - 2*x + 2)*(x^2 + 2*x + 2)`.
-/
syntax (name := casFactorCommand) "#cas" "[" &"factor" "]" term : command

/-- `#cas [trigExpand] e` expands the sines and cosines of sums, differences and double angles in
`e`.

## Theorem
For the variables `x₁, …, xₙ` of `e` and the printed expansion `e'`, the report proves
`∀ x₁ … xₙ : ℝ, e = e'` about `Real.sin` and `Real.cos`, by the addition and double-angle
formulas.

## Conditions and limits
`sin (a + b)`, `cos (a + b)`, `sin (a - b)`, `cos (a - b)`, `sin (2 * a)` and `cos (2 * a)` are
expanded, and the result is simplified. Other expressions, such as `sin (3 * x)` or `x ^ 2`, are
printed unchanged.

## Options
None.

## Examples
```lean
#cas [trigExpand] (sin (x + y))
```
```output
Output (scalar ℝ): sin(x)*cos(y) + cos(x)*sin(y)
```
```lean
#cas [trigExpand] (cos (2*x))
```
```output
Output (scalar ℝ): cos(x)^2 - sin(x)^2
```
```lean
#cas [trigExpand] (cos (x - y) * sin (2 * y))
```
```output
Output (scalar ℝ): (cos(x)*cos(y) + sin(x)*sin(y))*(2*sin(y)*cos(y))
```

## In a proof
```lean
theorem trigExpand_sin_add (x y : ℝ) :
    Real.sin (x + y) = Real.sin x * Real.cos y + Real.cos x * Real.sin y := by
  cas
```

## See also
Mathematica `TrigExpand`, SymPy `expand_trig`. The modes `expand`, `fullSimplify` and
`simplify`.

## Possible issues
```lean
#cas [trigExpand] (sin (3*x))
```
```output
Output (scalar ℝ): sin(3*x)
```
A multiple angle other than a double angle is not expanded, and the report proves the trivial
identity `sin (3 * x) = sin (3 * x)`.
-/
syntax (name := casTrigExpandCommand) "#cas" "[" &"trigExpand" "]" term : command

elab_rules : command
  | `(#cas [fullSimplify $[$c:ident]?] $expr:term) => do
      let complexity ← match c.map (·.getId) with
        | none | some `leafCount => pure FullSimplify.Complexity.leafCount
        | some `depth => pure .depth
        | some `length => pure .length
        | some other => throwError "unknown complexity function {other}; \
            use leafCount, depth or length"
      FullSimplify.logRanked expr .full complexity expr
  | `(#cas [expand] $expr:term) => FullSimplify.logRanked expr .expand .leafCount expr
  | `(#cas [factor] $expr:term) => do
      unless ← Tactic.RouteRegistry.runCommandBackends `factor (← getRef) do
        FullSimplify.logRanked expr .factor .leafCount expr
  | `(#cas [trigExpand] $expr:term) =>
      FullSimplify.logRanked expr .trigExpand .leafCount expr

end CAS.Command
