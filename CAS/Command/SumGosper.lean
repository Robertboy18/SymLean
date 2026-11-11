/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.Sum
public import CAS.Command.ParamSystems
public import CAS.Polynomial.ExprCoefficients
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses

/-!
# Sums of hypergeometric terms: Gosper's algorithm for `#cas [sum k a n]`

For a summand `t k = cᵏ R(k)` with a rational function `R` and a rational `c > 0` (sums of such
terms are split by `c`), Gosper's algorithm decides whether `∑ t k` has a closed form
`z (n + 1) - z a` with `z k = S(k) t k` and `S` rational. The ratio `t (k + 1) / t k` is written
`a(k) / b(k) · p(k + 1) / p(k)` with `gcd (a(k), b(k + h)) = 1` for every `h ≥ 0`, and a
polynomial solution `x` of `a(k) x(k + 1) - b(k - 1) x(k) = p(k)` gives
`z k = b(k - 1) x(k) / p(k) · t k`, with `z (k + 1) - z k = t k`. Telescoping rational sums such
as `∑ 1 / (k (k + 1))` are the case `c = 1`.

The closed form is proved for every `n ≥ a - 1` by induction; the algorithm only proposes it. For a
rational closed form the kernel checks the step on coefficient lists
(`Verified.Expr.eval_add_eval_eq_of_telescopes`), which stays fast at degree 70, where `ring` does
not finish; otherwise the step is `field_simp` and `ring`. The shifts `h` are all the nonnegative
integer roots of the resultant of `a(k)` and `b(k + h)`, and `x` is searched up to the degree bound
of Gosper's algorithm, so when no `x` exists the sum has no closed form in hypergeometric terms, as
for `∑ 1 / k`, and the command says so.

The work is bounded where it grows. A shift is a difference of roots of `b` and `a`, so it is at
most the sum of their root bounds; each `h` up to that bound is tested by a gcd, which a gcd
modulo a prime filters, when that takes at most `maxShiftWork` coefficient operations, and
otherwise the shifts are the integer roots of a resultant of degree at most `maxDegree`. The
command refuses, and says what it would need, when neither search is within its bound, when `p`
or `x` would have a degree above `maxDegree`, and when the root search leaves a shift undecided.
The kernel check of the closed form grows with its degree: the shift `96` takes about 40 s. The
search checks the heartbeat limit at each step, the linear system for `x` included, so that
`maxHeartbeats` stops it as well, except while `RootIsolation.rationalRoots` finds the integer roots
of the resultant: at degree 100, for `1 / ((k ^ 10 + 10 ^ 40) ((k + 1) ^ 10 + 10 ^ 40))`, that
takes about two minutes.
-/

public meta section

namespace CAS.Command.SumGosper

open Lean Elab Command Meta Term
open CAS.Command.InfoView
open CAS.Command.SpecialFunctions
open CAS.Command.Algebra (Dense)
open CAS.Verified.Expr

/-- The largest degree of `p` and of `x` in Gosper's algorithm that the command works with, and of
the resultant whose integer roots are the shifts, when they are not tested one by one. -/
def maxDegree : Nat := 100

/-- The largest shift bound, and the most coefficient operations,
`(bound + 1) (deg a + deg b + 1)²`, for which the command tests the shifts one by one. -/
def maxShifts : Nat := 10000

/-- See `maxShifts`. -/
def maxShiftWork : Nat := 2 ^ 22

/-- `1`. -/
def pOne : Dense := #[1]
/-- `k`. -/
def pVar : Dense := #[0, 1]

/-- `p (k + h)`. -/
def pShift (p : Dense) (h : ℚ) : Dense :=
  p.foldr (fun c acc ↦ Dense.add (Dense.mul acc #[h, 1]) #[c]) #[]

/-- The degree of `p`, and `0` for the zero polynomial. -/
def pDeg (p : Dense) : Nat := (Dense.trim p).size - 1

/-- A rational function `N / D`, reduced and with monic `D`. -/
def reduce (N D : Dense) : Dense × Dense :=
  let g := Dense.gcd N D
  let N := (Dense.divMod N g).1
  let D := (Dense.divMod D g).1
  let l := Dense.lead D
  (Dense.trim (Dense.scale (1 / l) N), Dense.trim (Dense.scale (1 / l) D))

/-- Terms `cᵏ N(k) / D(k)` grouped by `c`. -/
abbrev Hyper := List (ℚ × Dense × Dense)

/-- `a + b` when the terms of `a` have distinct `c`: the rational functions of equal `c` are
added and reduced. -/
def hAdd (a b : Hyper) : Hyper :=
  b.foldl (fun total (c, N, D) ↦
    match total.find? (·.1 == c) with
    | some (_, N', D') =>
        let (N'', D'') := reduce (Dense.add (Dense.mul N D') (Dense.mul N' D)) (Dense.mul D D')
        total.filter (·.1 != c) ++ [(c, N'', D'')]
    | none => total ++ [(c, N, D)]) a

/-- `q a`. -/
def hScale (q : ℚ) (a : Hyper) : Hyper := a.map fun (c, N, D) ↦ (c, Dense.scale q N, D)

/-- `a b`: the products `(c₁ c₂)ᵏ N₁ N₂ / (D₁ D₂)` of all pairs of terms, reduced
and summed by `hAdd`. -/
def hMul (a b : Hyper) : Hyper := Id.run do
  let mut out : Hyper := []
  for (c₁, N₁, D₁) in a do
    for (c₂, N₂, D₂) in b do
      let (N, D) := reduce (Dense.mul N₁ N₂) (Dense.mul D₁ D₂)
      out := hAdd out [(c₁ * c₂, N, D)]
  return out

/-- The constant `q` as `1ᵏ q / 1`. -/
def hConst (q : ℚ) : Hyper := [(1, #[q], #[1])]

/-- The summand as a sum of hypergeometric terms `cᵏ R(k)`. -/
partial def toHyper : Verified.Expr (Fin 1) → Option Hyper
  | .nat n => some (hConst n)
  | .int n => some (hConst n)
  | .rat p q => if q = 0 then none else some (hConst ((p : ℚ) / q))
  | .var _ => some [(1, pVar, pOne)]
  | .add a b => return hAdd (← toHyper a) (← toHyper b)
  | .sub a b => return hAdd (← toHyper a) (hScale (-1) (← toHyper b))
  | .neg a => return hScale (-1) (← toHyper a)
  | .mul a b => return hMul (← toHyper a) (← toHyper b)
  | .pow a n => do
      let base ← toHyper a
      return (List.range n).foldl (fun total _ ↦ hMul total base) (hConst 1)
  | .div a b => do
      -- Only a single term divides.
      match ← toHyper b with
      | [(c, N, D)] =>
          if Dense.isZero N then none
          else
            let (N', D') := reduce D N
            return hMul (← toHyper a) [(1 / c, N', D')]
      | _ => none
  | .rpow a (.var _) => do
      match ← toHyper a with
      | [(1, N, D)] =>
          if pDeg N = 0 && pDeg D = 0 && Dense.lead D ≠ 0 then
            let r := Dense.lead N / Dense.lead D
            if r > 0 then return [(r, pOne, pOne)] else none
          else none
      | _ => none
  | _ => none

/-- Solve a rational linear system `M v = rhs` (least-squares free: exact, possibly
overdetermined), returning a solution when it is consistent. The heartbeat limit is checked at
each column. -/
def solveSystem (M : Array (Array ℚ)) (rhs : Array ℚ) (n : Nat) : CoreM (Option (Array ℚ)) := do
  let rows := M.size
  let mut A := (Array.range rows).map fun i ↦ (M.getD i #[]).push (rhs.getD i 0)
  let mut pivots : Array Nat := #[]
  let mut row := 0
  for col in [0:n] do
    checkSystem "sum"
    if row ≥ rows then break
    let some pr := (List.range rows).find? fun r ↦ r ≥ row && (A.getD r #[]).getD col 0 != 0
      | continue
    let pivotRow := A.getD pr #[]
    A := A.set! pr (A.getD row #[])
    A := A.set! row pivotRow
    let pv := pivotRow.getD col 0
    let prow := pivotRow.map (· / pv)
    A := A.set! row prow
    for r in [0:rows] do
      if r != row then
        let f := (A.getD r #[]).getD col 0
        if f != 0 then
          A := A.set! r ((Array.range (n + 1)).map fun k ↦
            (A.getD r #[]).getD k 0 - f * prow.getD k 0)
    pivots := pivots.push col
    row := row + 1
  -- Consistency.
  for r in [row:rows] do
    if (A.getD r #[]).getD n 0 != 0 then return none
  let mut sol : Array ℚ := Array.replicate n 0
  for i in [0:pivots.size] do
    sol := sol.set! (pivots.getD i 0) ((A.getD i #[]).getD n 0)
  return some sol

/-- The resultant of `f` and `g`, by Euclid's algorithm. -/
partial def resultant (f g : Dense) : ℚ :=
  let f := Dense.trim f
  let g := Dense.trim g
  if f.isEmpty || g.isEmpty then 0
  else if pDeg g = 0 then Dense.lead g ^ pDeg f
  else
    let r := (Dense.divMod f g).2
    if Dense.isZero r then 0
    else (-1) ^ (pDeg f * pDeg g) * Dense.lead g ^ (pDeg f - pDeg r) * resultant g r

/-- The polynomial of degree below `values.size` through the points `(i, values[i])`, by
Lagrange's formula. The heartbeat limit is checked at each point. -/
def interpolate (values : Array ℚ) : CoreM Dense := do
  let mut total : Dense := #[]
  for i in [0:values.size] do
    checkSystem "sum"
    let mut term : Dense := #[values[i]!]
    for j in [0:values.size] do
      if j != i then
        term := Dense.scale (1 / ((i : ℚ) - j)) (Dense.mul term #[-(j : ℚ), 1])
    total := Dense.add total term
  return Dense.trim total

/-- The least `r` with `q ≤ r ^ i`, for `i ≥ 1`. -/
def rootCeil (q : ℚ) (i : Nat) : Nat := Id.run do
  let m := q.ceil.toNat
  if m ≤ 1 then return m
  -- `lo ^ i < m ≤ hi ^ i`.
  let mut lo := 1
  let mut hi := 2 ^ (Nat.log2 m / i + 1)
  while lo + 1 < hi do
    let middle := (lo + hi) / 2
    if m ≤ middle ^ i then hi := middle else lo := middle
  return hi

/-- Fujiwara's bound on the absolute values of the complex roots of `p`,
`2 max |cₙ₋ᵢ / cₙ| ^ (1 / i)`, rounded up, and `0` for a constant. -/
def rootBound (p : Dense) : Nat :=
  let p := Dense.trim p
  let n := p.size - 1
  let l := Dense.lead p
  2 * (List.range n).foldl (fun m i ↦ max m (rootCeil |p.getD (n - 1 - i) 0 / l| (i + 1))) 0

/-- The primes below `2 ^ 31` that the shift test reduces modulo. -/
def primes : List Nat := [2147483647, 2147483629, 2147483587]

/-- The coefficients modulo `m` of a polynomial with integer coefficients, constant term first. -/
def modCoefficients (m : Nat) (p : Dense) : Array Nat := p.map fun c ↦ (c.num % (m : ℤ)).toNat

/-- `p` without its zero coefficients at the top. -/
def trimMod (p : Array Nat) : Array Nat := Id.run do
  let mut p := p
  while p.back? == some 0 do p := p.pop
  return p

/-- `b ^ e` modulo `m`. -/
def powMod (b e m : Nat) : Nat := Id.run do
  let mut result := 1
  let mut b := b % m
  let mut e := e
  while e > 0 do
    if e % 2 == 1 then result := result * b % m
    b := b * b % m
    e := e / 2
  return result

/-- `p (k + h)` modulo `m`, by Horner's rule. -/
def shiftMod (m : Nat) (p : Array Nat) (h : Nat) : Array Nat := Id.run do
  let mut result : Array Nat := #[]
  for c in p.reverse do
    -- `result (k + h) + c`, with `result` already in `k`.
    let mut next := Array.replicate (result.size + 1) 0
    for i in [0:result.size] do
      next := next.modify (i + 1) (fun v ↦ (v + result[i]!) % m)
      next := next.modify i (fun v ↦ (v + result[i]! * h) % m)
    result := next.modify 0 (fun v ↦ (v + c) % m)
  return trimMod result

/-- The degree of the gcd of `p` and `q` modulo the prime `m`, by Euclid's algorithm, and `0`
when both are zero. -/
def gcdDegreeMod (m : Nat) (p q : Array Nat) : Nat := Id.run do
  let mut p := trimMod p
  let mut q := trimMod q
  let mut fuel := p.size + q.size + 2
  while q.size > 0 && fuel > 0 do
    fuel := fuel - 1
    -- `p mod q`.
    let inverse := powMod q.back! (m - 2) m
    let mut r := p
    let mut steps := r.size + 1
    while r.size ≥ q.size && steps > 0 do
      steps := steps - 1
      let factor := r.back! * inverse % m
      let offset := r.size - q.size
      for i in [0:q.size] do
        r := r.modify (offset + i) (fun v ↦ (v + (m - factor) * q[i]!) % m)
      r := trimMod r
    p := q
    q := r
  return p.size - 1

/-- The dispersion set of `a` and `b`: the integers `h ≥ 0` at which `a(k)` and `b(k + h)` have a
common root, in increasing order. Such an `h` is `β - α` for roots `α` of `a` and `β` of `b`, so at
most `rootBound a + rootBound b`. When that bound is small (`maxShifts`, `maxShiftWork`), each `h`
up to it is tested: the gcd of the primitive integer multiples of `a` and `b(k + h)` modulo a prime
that does not divide the leading coefficient of the first has positive degree whenever the gcd
over `ℚ` has, so that a constant gcd modulo the prime rules `h` out, and `Dense.gcd` decides the
others. Otherwise the shifts are the nonnegative integer roots of the resultant
`R(h) = res_k (a(k), b(k + h))`, a polynomial in `h` of degree at most `deg a · deg b`, here
interpolated from its values at `h = 0, …, deg a · deg b`, when that degree is at most
`maxDegree`. The second component says whether the root search decided every root, and the error
says which search the command does not do. -/
def dispersion (a b : Dense) : ExceptT String CoreM (List Nat × Bool) := do
  if pDeg a == 0 || pDeg b == 0 then return ([], true)
  let bound := rootBound a + rootBound b
  let work := (bound + 1) * (pDeg a + pDeg b + 1) ^ 2
  if bound ≤ maxShifts ∧ work ≤ maxShiftWork then
    let a' := RootIsolation.primitive a
    let b' := RootIsolation.primitive b
    let filter := (primes.find? fun (m : Nat) ↦ (Dense.lead a').num % (m : ℤ) ≠ 0).map fun m ↦
      (m, modCoefficients m a', modCoefficients m b')
    let mut shifts : List Nat := []
    for h in [0:bound + 1] do
      checkSystem "sum"
      let candidate := match filter with
        | some (m, am, bm) => gcdDegreeMod m am (shiftMod m bm h) ≥ 1
        | none => true
      if candidate && pDeg (Dense.gcd a (pShift b h)) ≥ 1 then shifts := shifts ++ [h]
    return (shifts, true)
  let degree := pDeg a * pDeg b
  if degree > maxDegree then
    throwThe String s!"Gosper's algorithm needs the integer shifts between the factors of this \
      summand's ratio, which may be up to {bound} apart; the command tests them one by one for \
      at most {maxShifts} shifts and {maxShiftWork} coefficient operations, here {work}, and \
      finds them as the integer roots of a resultant up to degree {maxDegree}, here {degree}"
  let mut values := #[]
  for h in [0:degree + 1] do
    checkSystem "sum"
    values := values.push (resultant a (pShift b h))
  let (roots, _, complete) := RootIsolation.rationalRoots (← interpolate values).toList
  let shifts := roots.filterMap fun (r, _) ↦
    if r.den = 1 && 0 ≤ r.num then some r.num.toNat else none
  return (shifts.mergeSort (· ≤ ·), complete)

/-- The degree of `p`, and `-1` for the zero polynomial. -/
def degree (p : Dense) : Int := if Dense.isZero p then -1 else pDeg p

/-- Gosper's algorithm for `cᵏ N(k) / D(k)`: `some S` for the rational function `S` with
`z k = S(k) t k` and `z (k + 1) - z k = t k`, or `none` when there is no such `S`, which proves
that the sum has no closed form in hypergeometric terms. The shifts are the whole dispersion set,
and the degree of `x` is one of those of Petkovšek, Wilf and Zeilberger, *A = B*, chapter 5: with
`s = deg (a(k) + b(k - 1))` and `t = deg (a(k) - b(k - 1))`, `deg x = deg p - t` when `t ≥ s`,
and otherwise `deg x` is `deg p - s + 1` or the integer `L` at which the top coefficients cancel.
The least of them at which the equation has a solution is the degree of its solutions of least
degree. The error is a search that this command does not finish, and says which. -/
def gosper (c : ℚ) (N D : Dense) : ExceptT String CoreM (Option (Dense × Dense)) := do
  -- `t (k + 1) / t k = c N(k + 1) D(k) / (N(k) D(k + 1))`.
  let (A, B) := reduce (Dense.scale c (Dense.mul (pShift N 1) D)) (Dense.mul N (pShift D 1))
  let (shifts, complete) ← dispersion A B
  unless complete do
    throwThe String "Gosper's algorithm did not finish for this summand: the root search left \
      some shifts between the factors of its ratio undecided"
  let mut a := A
  let mut b := B
  let mut p : Dense := pOne
  for h in shifts do
    let mut again := true
    while again do
      checkSystem "sum"
      let g := Dense.gcd a (pShift b h)
      if pDeg g ≥ 1 then
        if pDeg p + pDeg g * h > maxDegree then
          throwThe String s!"Gosper's algorithm needs a polynomial of degree at least \
            {pDeg p + pDeg g * h} for this summand, whose ratio has factors {h} apart, and the \
            command searches up to degree {maxDegree}"
        a := (Dense.divMod a g).1
        b := (Dense.divMod b (pShift g (-(h : ℚ)))).1
        for i in [1:h + 1] do
          p := Dense.mul p (pShift g (-(i : ℚ)))
      else again := false
  -- `a(k) x(k + 1) - b(k - 1) x(k) = p(k)`.
  let bm := pShift b (-1)
  let plus := Dense.add a bm
  let minus := Dense.sub a bm
  -- The degrees that `x` can have.
  let degrees : List Int :=
    if degree minus ≥ degree plus then [degree p - degree minus]
    else
      let s := pDeg plus
      let L := -2 * (Dense.trim minus).getD (s - 1) 0 / Dense.lead plus
      [degree p - s + 1] ++ if L.den = 1 then [L.num] else []
  let degrees := (degrees.filter (0 ≤ ·)).eraseDups.mergeSort (· ≤ ·)
  for d in (degrees.filter (· ≤ (maxDegree : ℤ))).map Int.toNat do
    checkSystem "sum"
    -- Unknown coefficients `x₀, …, x_d`.
    let columns := (Array.range (d + 1)).map fun i ↦
      let mono : Dense := (Array.replicate i 0).push 1
      Dense.sub (Dense.mul a (pShift mono 1)) (Dense.mul bm mono)
    let size := max (columns.foldl (fun m (col : Dense) ↦ max m col.size) 0) p.size
    let M := (Array.range size).map fun r ↦ columns.map fun col ↦ col.getD r 0
    let rhs := (Array.range size).map fun r ↦ p.getD r 0
    if let some x ← solveSystem M rhs (d + 1) then
      let xs := Dense.trim x
      if !xs.isEmpty then
        -- `S(k) = b(k - 1) x(k) / p(k)`.
        return some (reduce (Dense.mul bm xs) p)
  if let some bound := degrees.find? (· > (maxDegree : ℤ)) then
    throwThe String s!"Gosper's algorithm needs a polynomial of degree {bound} for this \
      summand, and the command searches up to degree {maxDegree}"
  return none

/-- The integer roots of `p` that `Sum.rationalRoots` finds. -/
def integerRoots (p : Dense) : List ℤ :=
  (Sum.rationalRoots (Dense.trim p).toList).1.filterMap fun (r, _) ↦
    if r.den = 1 then some r.num else none

/-- `∑ cᵢ kᵢ` as an expression. -/
def polyE (p : Dense) : Verified.Expr (Fin 1) :=
  let p := Dense.trim p
  if p.isEmpty then .nat 0 else Sum.polyExpr p

/-- `N / D` as an expression, with integer coefficients in the denominator. -/
def ratFunE (N D : Dense) : Verified.Expr (Fin 1) :=
  let D := Dense.trim D
  if D.size = 1 then
    let d := D.getD 0 1
    polyE (Dense.scale (1 / d) N)
  else
    let scale := (N ++ D).foldl (fun l c ↦ Nat.lcm l c.den) 1
    .div (polyE (Dense.scale scale N)) (polyE (Dense.scale scale D))

/-- Run `#cas [sum k a n] f` for hypergeometric summands. -/
def logGosper (ref : Syntax) (k : TSyntax `ident) (aStx : Syntax) (n : TSyntax `ident)
    (input : Syntax) : CommandElabM Unit := do
  let a ← parseRational "sum" aStx
  unless a.den = 1 && 0 ≤ a do throwUnsupportedSyntax
  let aNat := a.num.toNat
  let reified ← Sum.parseSummand input k.getId
  let f : Verified.Expr (Fin 1) ← match reified with
    | ⟨[_], expression, _⟩ => pure expression
    | _ => throwUnsupportedSyntax
  -- Polynomial and geometric summands are treated by `CAS.Command.Sum`.
  if (Sum.toGeoPoly f (geometricQuotients := true)).isSome then throwUnsupportedSyntax
  let some groups := toHyper f | throwUnsupportedSyntax
  -- Each group `cᵏ N / D`: `z k = cᵏ W(k)` with `W = S N / D`.
  let mut rational : Dense × Dense := (#[], #[1])
  let mut geometric : List (ℚ × Dense × Dense) := []
  let mut constant : ℚ := 0
  for (c, N, D) in groups do
    if Dense.isZero N then continue
    for r in integerRoots D do
      if r ≥ (aNat : ℤ) then
        throwErrorAt input "sum: the summand is undefined at {k.getId} = {r}"
    let (U, V) ← match ← liftCoreM (gosper c N D).run with
      | .ok (some solution) => pure solution
      | .ok none => throwErrorAt input "sum: Gosper's algorithm finds no closed form in \
          hypergeometric terms for this summand"
      | .error reason => throwErrorAt input "sum: {reason}"
    let (WN, WD) := reduce (Dense.mul U N) (Dense.mul V D)
    for r in integerRoots WD do
      if r ≥ (aNat : ℤ) then
        throwErrorAt input "sum: the closed form is undefined at {k.getId} = {r}"
    let za := c ^ aNat * Dense.eval WN aNat / Dense.eval WD aNat
    constant := constant + za
    -- `z (n + 1) = c ^ (n + 1) W (n + 1)`.
    let WN' := pShift WN 1
    let WD' := pShift WD 1
    if c = 1 then
      let (RN, RD) := rational
      rational := reduce (Dense.add (Dense.mul RN WD') (Dense.mul WN' RD)) (Dense.mul RD WD')
    else geometric := geometric ++ [(c, Dense.scale c WN', WD')]
  -- `F n = ∑ z (n + 1) - ∑ z a`.
  let (RN, RD) := rational
  let (RN, RD) := reduce (Dense.sub RN (Dense.scale constant RD)) RD
  let mut F : Verified.Expr (Fin 1) := ratFunE RN RD
  for (c, GN, GD) in geometric do
    let term : Verified.Expr (Fin 1) :=
      .mul (.rpow (ratExpr c) (.var 0)) (ratFunE GN GD)
    F := if Dense.isZero RN then term else .add F term
  let aLit : TSyntax `num := Syntax.mkNumLit (toString aNat)
  let lemmas := Series.seriesCleanLemmas ++ [``Real.rpow_natCast, ``Nat.cast_ofNat,
    ``Matrix.cons_val_zero, ``Int.cast_ofNat, ``Int.cast_neg, ``Nat.cast_id]
  let proof ← liftTermElabM do
    let fT ← exprToSyntax (← quoteVerifiedExpr f)
    let FT ← exprToSyntax (← quoteVerifiedExpr F)
    let simpEval ← `(tactic| simp only [Verified.Expr.eval, Matrix.cons_val_zero,
      Matrix.cons_val_fin_one, Real.rpow_natCast, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero,
      Int.cast_ofNat, Int.cast_neg, Int.cast_one, Int.cast_zero])
    let summand ← `(fun $k:ident : ℕ ↦ Verified.Expr.eval ![($k : ℝ)] $fT)
    let nT : TSyntax `term := ⟨n.raw⟩
    let body ← `(∑ $k:ident ∈ Finset.Icc $aLit $nT, $summand $k =
      Verified.Expr.eval ![($nT : ℝ)] $FT)
    -- For rational `F` and `f` the kernel checks the step on coefficient lists, and only the
    -- denominators are left to tactics; `ring` would cost a proof term for each product of two
    -- monomials, too many for a closed form of degree 70.
    let step ← `(tactic| first
      | (refine Verified.Expr.eval_add_eval_eq_of_telescopes (by push_cast; ring)
            (by decide +kernel) ?_ ?_ ?_ <;>
          (simp only [Verified.Expr.den]
           $simpEval:tactic
           push_cast
           first | positivity | (ring_nf; positivity)))
      | ($simpEval:tactic
         push_cast
         ring_nf
         field_simp
         ring))
    if aNat ≤ 1 then
      let statement ← `(∀ $n:ident : ℕ, $body)
      let zeroCase ← if aNat = 0 then `(tactic| rw [Finset.Icc_self, Finset.sum_singleton])
        else `(tactic| rw [Finset.Icc_eq_empty (by omega)])
      let proofStx ← `(by
        intro $n:ident
        induction $n:ident with
        | zero =>
            $zeroCase:tactic
            $simpEval:tactic
            norm_num
        | succ m ih =>
            rw [Finset.sum_Icc_succ_top (by omega), ih]
            $step:tactic)
      elabCheckedProof "sum" statement proofStx
    else
      let base : TSyntax `num := Syntax.mkNumLit (toString (aNat - 1))
      let statement ← `(∀ $n:ident : ℕ, $base ≤ $nT → $body)
      let j := mkIdent `j
      let proofStx ← `(by
        intro $n:ident hn
        obtain ⟨$j:ident, hj⟩ : ∃ $j:ident : ℕ, $nT = $j + $base := ⟨$nT - $base, by omega⟩
        rw [hj]
        clear hj hn
        induction $j:ident with
        | zero =>
            rw [Finset.Icc_eq_empty (by omega)]
            $simpEval:tactic
            norm_num
        | succ m ih =>
            rw [show m + 1 + $base = m + $base + 1 by omega,
              Finset.sum_Icc_succ_top (by omega), ih]
            $step:tactic)
      elabCheckedProof "sum" statement proofStx
  let proof ← liftTermElabM do
    let cleaned ← Digits.cleanProof proof lemmas [``Verified.Expr.univariateEval]
      (simprocs := true)
    let cleaned ← Digits.evaluateNumerals cleaned
    let named := Digits.restoreNames (← inferType proof) (← inferType cleaned)
    let cleaned ← mkExpectedTypeHint cleaned named
    CAS.Tactic.Explanation.kernelCheckedProof "sum" named cleaned
  let report ← liftTermElabM do
    evidenceReportMessage
      #[← CAS.Tactic.Explanation.UncheckedExplanationStep.ofProof
        "Closed form for every upper bound, from Gosper's algorithm" proof]
  let answer ← liftTermElabM do
    let some rhs ← Sum.equationRhs (← inferType proof) | pure "see the statement"
    pure s!"{rhs}"
  logReport ref {
    domain := s!"{k.getId} ∈ [{aNat}, {n.getId}]"
    input := reified.render
    inputType := "hypergeometric summand"
    output := answer
    outputType := "closed form (Gosper)"
  } #[report]

end CAS.Command.SumGosper

namespace CAS.Command

open Lean Elab Command

elab_rules : command
  | `(#cas [sum $k:ident $a:term $n:ident] $f:term) => SumGosper.logGosper f k a n f

end CAS.Command
