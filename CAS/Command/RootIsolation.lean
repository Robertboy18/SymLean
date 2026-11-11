/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.Algebra.Dense
public import CAS.Polynomial.RealRoot.SignReduce
public meta import CAS.Polynomial.RealRoot.SignReduce

/-!
# Real root isolation

The search behind `#cas [roots]`, `#cas [reduce]`, `#cas [solve]`, `#cas [minimize]` and the sign
route of bare `cas`. It proposes a `RootListCertificate`, which the kernel checks with
`realRootCheck`; nothing here is trusted. The search is kept in the core library, so that these
commands work without Hex.

`rationalRoots` finds the rational roots of a polynomial with their multiplicities. Each real root
of the square-free part is isolated by `cover`, and the isolating interval is narrowed until it
holds at most one rational whose denominator divides the leading coefficient of the primitive
square-free part; by the rational root theorem every rational root is such a number, so the
coefficients are never factored and no divisor is enumerated.

`generate` splits off the rational roots with their multiplicities (the identity
`p = c · ∏ (X - rᵢ) · q`), takes the square-free radical of `q` when `q` has repeated factors,
bounds its roots by a Cauchy bound `B`, and covers `[-B, B]` with root-free cells and root cells.
The rational roots and any requested marks are cell boundaries. Each root cell is refined to a
decimal interval of width `10 ^ (-digits)`, or to an exact cell when a bisection point is the root.
The number of cells is bounded by a budget rather than a bisection depth.
-/

public meta section

namespace CAS.Command.RootIsolation

open CAS.Polynomial CAS.Polynomial.RealRoot
open CAS.Command.Algebra

/-- A direction for which `[u, v]` is a root bracket of `p`, if any. -/
def bracketDirection? (p : Sparse.Univariate) (u v : ℚ) : Option Direction :=
  if RootBracket.valid p ⟨cellInterval u v, .increasing⟩ then some .increasing
  else if RootBracket.valid p ⟨cellInterval u v, .decreasing⟩ then some .decreasing
  else none

/-- A point of `(u, v)` where `p` is nonzero: the midpoint when it is not a root, and otherwise
the first nonroot among the odd multiples of `(v - u) / 2 ^ j`, for `j = 2, 3, …`. -/
def nonRootNear (p : Sparse.Univariate) (u v : ℚ) : ℚ := Id.run do
  let mut trials := 0
  for j in [1:64] do
    for i in [0:2 ^ (j - 1)] do
      let c := u + (v - u) * ((2 * i + 1 : Nat) : ℚ) / (2 : ℚ) ^ j
      if Sparse.evalRat p c != 0 || trials > 4096 then return c
      trials := trials + 1
  return (u + v) / 2

/-- The cell of the root in the bracket `[u, v]`: a decimal interval of width `10 ^ (-digits)`
with nonroot endpoints outside `avoid` when bisection reaches one that is a bracket, a narrower
bisection interval otherwise, and an exact cell when a bisection point is the root. -/
def refine (p : Sparse.Univariate) (avoid : List ℚ) (direction : Direction) (digits : Nat)
    (u v : ℚ) : Except String RootCell := Id.run do
  let increasing := direction == .increasing
  let scale : ℚ := 10 ^ digits
  let ok (a b : ℚ) : Bool :=
    u ≤ a && a < b && b ≤ v && Sparse.evalRat p a != 0 && Sparse.evalRat p b != 0 &&
      !avoid.contains a && !avoid.contains b && RootBracket.valid p ⟨cellInterval a b, direction⟩
  let mut lo := u
  let mut hi := v
  let mut extra := 0
  for _ in [0:4096] do
    if hi - lo < 1 / scale then
      let k := (lo * scale).floor
      let a : ℚ := (k : ℚ) / scale
      let b : ℚ := ((k : ℚ) + 1) / scale
      if hi ≤ b && ok a b then return .ok (RootCell.root direction a b)
      if extra ≥ 40 then
        if ok lo hi then return .ok (RootCell.root direction lo hi)
        break
      extra := extra + 1
    let m := (lo + hi) / 2
    let value := Sparse.evalRat p m
    if value = 0 then return .ok (RootCell.exact direction m)
    if (value < 0) == increasing then lo := m else hi := m
  return .error s!"could not refine the root in [{u}, {v}]"

/-- Cover `[u, v]` with consecutive cells for the square-free polynomial `p`: root-free cells, and
root brackets, refined by `refine` when `refineRoots` holds. The points of `splits` inside
`(u, v)` are cell boundaries; the endpoints and the splits must not be roots of `p`. A cell that
is neither free nor a bracket is split at `nonRootNear`. The search stops with an error after
`budget` cells. -/
def cover (p : Sparse.Univariate) (avoid : List ℚ) (refineRoots : Bool) (digits : Nat)
    (splits : List ℚ) (u v : ℚ) (budget : Nat) : Except String (List (ℚ × RootCell)) := do
  let inside := ((splits.filter fun s ↦ u < s && s < v).mergeSort (· ≤ ·)).eraseDups
  let mut pending := inside ++ [v]
  let mut left := u
  let mut cells : Array (ℚ × RootCell) := #[]
  let mut steps := 0
  while true do
    match pending with
    | [] => break
    | right :: rest =>
      steps := steps + 1
      if steps > 4 * budget + 64 || cells.size > budget then
        throw s!"the root certificate needs more than {budget} cells"
      if rootFree p (cellInterval left right) then
        cells := cells.push (right, RootCell.free)
        left := right
        pending := rest
      else if let some direction := bracketDirection? p left right then
        let cell : RootCell ← if refineRoots then refine p avoid direction digits left right
          else pure (RootCell.root direction left right)
        cells := cells.push (right, cell)
        left := right
        pending := rest
      else
        pending := nonRootNear p left right :: pending
  return cells.toList

/-- The primitive integer multiple of `p`: integer coefficients without a common factor, with the
sign of `p`. -/
def primitive (p : Dense) : Dense :=
  let p := Dense.trim p
  let scale : Nat := p.foldl (fun l c ↦ Nat.lcm l c.den) 1
  let integers := p.map (· * (scale : ℚ))
  let content : Nat := integers.foldl (fun g c ↦ Nat.gcd g c.num.natAbs) 0
  if content = 0 then p else integers.map (· / (content : ℚ))

/-- The order of the reported rational roots: by the absolute value of the numerator, then by the
denominator, the positive root first. -/
def rootBefore (a b : ℚ) : Bool :=
  if a.num.natAbs != b.num.natAbs then a.num.natAbs < b.num.natAbs
  else if a.den != b.den then a.den < b.den
  else !(a < 0) || b < 0

/-- The rational root of `p` in the bracket `[u, v]`, if any, when every rational root of `p` is
an integer multiple of `1 / L`: bisection narrows the bracket below width `1 / L`, which leaves
one candidate. The flag says whether the search decided. -/
def rationalRootIn (p : Sparse.Univariate) (L : ℚ) (direction : Direction) (u v : ℚ) :
    Option ℚ × Bool := Id.run do
  let increasing := direction == .increasing
  let mut lo := u
  let mut hi := v
  for _ in [0:4096] do
    if (hi - lo) * L < 1 then
      let r : ℚ := ((lo * L).ceil : ℚ) / L
      if r ≤ hi && Sparse.evalRat p r == 0 then return (some r, true)
      return (none, true)
    let m := (lo + hi) / 2
    let value := Sparse.evalRat p m
    if value == 0 then return (some m, true)
    if (value < 0) == increasing then lo := m else hi := m
  return (none, false)

/-- The rational roots of `cs` (coefficients, constant term first) with their multiplicities, in
the order of `rootBefore` after the root `0`; the exact quotient of `cs` by their linear factors,
which keeps the leading coefficient of `cs`; and whether the search decided every isolating
interval. The zero polynomial and the constants have no roots. -/
def rationalRoots (cs : List ℚ) : List (ℚ × ℕ) × List ℚ × Bool := Id.run do
  let mut current := Dense.trim cs.toArray
  if current.size ≤ 1 then return ([], current.toList, true)
  let zeros := (current.toList.takeWhile (· == 0)).length
  let mut roots : List (ℚ × ℕ) := []
  if zeros > 0 then
    current := current.extract zeros current.size
    roots := [(0, zeros)]
  if current.size ≤ 1 then return (roots, current.toList, true)
  let squareFree :=
    primitive (Dense.divMod current (Dense.gcd current (Dense.derivative current))).1
  let S := Sparse.ofCoeffs squareFree.toList
  let lead := Dense.lead squareFree
  let L := if lead < 0 then -lead else lead
  let some bound := CauchyBoundCertificate.generate? S | return (roots, current.toList, false)
  let B := bound.1.bound
  let .ok cells := cover S [] false 0 [] (-B) B 4096 | return (roots, current.toList, false)
  let mut found : List ℚ := []
  let mut complete := true
  for (_, cell) in cells do
    match cell with
    | .root direction lo hi =>
        let (r?, decided) := rationalRootIn S L direction lo hi
        if let some r := r? then found := r :: found
        complete := complete && decided
    | .exact _ r => found := r :: found
    | .free => pure ()
  let mut result := roots
  for r in found.mergeSort rootBefore do
    let mut count := 0
    let mut fuel := current.size
    while fuel > 0 do
      fuel := fuel - 1
      let (q, remainder) := Dense.divMod current #[-r, 1]
      if !remainder.isEmpty then break
      current := q
      count := count + 1
    if count > 0 then result := result ++ [(r, count)]
  return (result, current.toList, complete)

/-- The root-list certificate of the nonzero polynomial `cs` (coefficients, constant term first),
with root intervals of width `10 ^ (-digits)`, and the locations of its real roots in increasing
order: the rational roots exactly, the others by their intervals. The points of `marks` that are
not roots become cell boundaries, so that no root interval contains them. -/
def generate (cs : List ℚ) (digits : Nat) (marks : List ℚ := []) (budget : Nat := 1024) :
    Except String (RootListCertificate × List RootLoc) := do
  if (Dense.trim cs.toArray).isEmpty then
    throw "the polynomial is zero; every real number is a solution"
  let (rational, rest, _) := rationalRoots cs
  let rest := Dense.trim rest.toArray
  let primitiveRest := primitive rest
  let quotient :=
    if Dense.lead primitiveRest < 0 then Dense.scale (-1) primitiveRest else primitiveRest
  let content := Dense.lead rest / Dense.lead quotient
  let roots := rational.flatMap fun (r, m) ↦ List.replicate m r
  let radical : Option RadicalCertificate ←
    if (Dense.gcd quotient (Dense.derivative quotient)).size ≤ 1 then pure none
    else match RadicalCertificate.generate? (Sparse.ofCoeffs quotient.toList) with
      | some radical => pure (some radical.1)
      | none => throw "could not compute the square-free part of the polynomial"
  let provisional : RootListCertificate :=
    { content, roots, quotient := quotient.toList, radical, bound := ⟨1, 0, []⟩, cells := [] }
  let covered := provisional.covered
  let some bound := CauchyBoundCertificate.generate? covered
    | throw "could not bound the roots of the polynomial"
  let B := bound.1.bound
  let splits := (marks ++ rational.map (·.1)).filter fun s ↦ Sparse.evalRat covered s != 0
  let cells ← cover covered (rational.map (·.1)) true digits splits (-B) B budget
  let cellLocs := cells.filterMap fun (_, cell) ↦ match cell with
    | .root _ lo hi => some (RootLoc.interval lo hi)
    | .exact _ r => some (RootLoc.exact r)
    | .free => none
  let exactLocs : List RootLoc := rational.map fun (r, _) ↦ RootLoc.exact r
  let locs := (exactLocs ++ cellLocs).mergeSort fun a b ↦ a.lower ≤ b.lower
  return ({ provisional with bound := bound.1, cells }, locs)

end CAS.Command.RootIsolation
