/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Data.Rat.Init

/-!
# Dense univariate polynomials over `ℚ`

`Dense` is the type of polynomials in one variable with rational coefficients that the commands
compute with: the array `#[c₀, c₁, …, cₙ]` stands for `c₀ + c₁ x + ⋯ + cₙ xⁿ`. The operations
accept arrays with trailing zero coefficients and return trimmed ones, so their results compare
with `==`; `#[]` is the zero polynomial.

The arithmetic is ring arithmetic (`add`, `sub`, `scale`, `mul`, `pow`), Euclidean division
(`divMod`, `gcd`, `xgcd`), the formal derivative, the Taylor shift `p (x + h)`, and evaluation by
Horner's rule. It runs at elaboration time and is not trusted: the commands state what they
compute as ordinary propositions and prove them separately.
-/

public meta section

namespace CAS.Command.Algebra

/-- A polynomial in one variable with rational coefficients, from the constant term up. The
operations below return it without trailing zero coefficients. -/
abbrev Dense := Array ℚ

namespace Dense

/-- Drop trailing zero coefficients. -/
def trim (p : Dense) : Dense := Id.run do
  let mut p := p
  while p.size > 0 && p.back! == 0 do
    p := p.pop
  return p

/-- The degree; `0` for the zero polynomial. -/
def degree (p : Dense) : Nat := (trim p).size - 1

/-- The leading coefficient; `0` for the zero polynomial. -/
def lead (p : Dense) : ℚ := (trim p).back?.getD 0

/-- Whether this is the zero polynomial. -/
def isZero (p : Dense) : Bool := (trim p).isEmpty

/-- `p + q`. -/
def add (p q : Dense) : Dense :=
  trim <| (Array.range (max p.size q.size)).map fun k ↦ p.getD k 0 + q.getD k 0

/-- `c p`. -/
def scale (c : ℚ) (p : Dense) : Dense := trim (p.map (c * ·))

/-- `p - q`. -/
def sub (p q : Dense) : Dense := add p (scale (-1) q)

/-- `p q`. -/
def mul (p q : Dense) : Dense := Id.run do
  if p.isEmpty || q.isEmpty then return #[]
  let mut out : Array ℚ := Array.replicate (p.size + q.size - 1) 0
  for i in [0:p.size] do
    for j in [0:q.size] do
      out := out.set! (i + j) (out[i + j]! + p[i]! * q[j]!)
  return trim out

/-- `p ^ k`. -/
def pow (p : Dense) : Nat → Dense
  | 0 => #[1]
  | k + 1 => mul p (pow p k)

/-- The quotient and remainder of `p` by a nonzero `q`: the pair `(s, r)` with `p = s q + r` and
`r` of smaller degree than `q`. Division by zero gives `(#[], p)`. -/
def divMod (p q : Dense) : Dense × Dense := Id.run do
  let q := trim q
  let mut r := trim p
  if q.isEmpty then return (#[], r)
  let dq := q.size - 1
  let lq := q.back!
  let mut quotient : Array ℚ := Array.replicate (r.size + 1) 0
  let mut fuel := r.size + 1
  while r.size > dq && fuel > 0 do
    fuel := fuel - 1
    let shift := r.size - 1 - dq
    let c := r.back! / lq
    quotient := quotient.set! shift c
    let mut r' := r
    for j in [0:q.size] do
      r' := r'.set! (shift + j) (r'[shift + j]! - c * q[j]!)
    r := trim (r'.pop)
  return (trim quotient, r)

/-- `p` divided by its leading coefficient; the zero polynomial stays zero. -/
def monic (p : Dense) : Dense := let p := trim p; if p.isEmpty then p else scale (1 / p.back!) p

/-- The monic greatest common divisor of `p` and `q`, by Euclid's algorithm; `#[]` when both are
zero. -/
def gcd (p q : Dense) : Dense :=
  go (p.size + q.size + 1) (trim p) (trim q)
where
  /-- Euclid's algorithm on `p` and `q`, the fuel bounding the number of divisions. Each division
  lowers the degree of the second argument, so `p.size + q.size + 1` divisions are enough. -/
  go : Nat → Dense → Dense → Dense
    | 0, p, _ => monic p
    | fuel + 1, p, q => if isZero q then monic p else go fuel q (divMod p q).2

/-- The extended gcd of `p` and `q`: the triple `(g, s, t)` with `g` their monic greatest common
divisor and `s p + t q = g`. For `p = q = 0` it is `(#[], #[1], #[])`. -/
def xgcd (p q : Dense) : Dense × Dense × Dense :=
  go (p.size + q.size + 2) (trim p) #[1] #[] (trim q) #[] #[1]
where
  /-- `(r, s, t)` divided by the leading coefficient of `r`, unchanged when `r` is zero. -/
  normalize (r s t : Dense) : Dense × Dense × Dense :=
    let c := lead r
    if c = 0 then (r, s, t) else (scale (1 / c) r, scale (1 / c) s, scale (1 / c) t)
  /-- Euclid's algorithm on remainders `r₀` and `r₁` with `s₀ p + t₀ q = r₀` and
  `s₁ p + t₁ q = r₁`, the fuel bounding the number of divisions; the last nonzero remainder and
  its cofactors are divided by its leading coefficient. -/
  go : Nat → Dense → Dense → Dense → Dense → Dense → Dense → Dense × Dense × Dense
    | 0, r₀, s₀, t₀, _, _, _ => normalize r₀ s₀ t₀
    | fuel + 1, r₀, s₀, t₀, r₁, s₁, t₁ =>
        if isZero r₁ then normalize r₀ s₀ t₀
        else
          let (quotient, r₂) := divMod r₀ r₁
          go fuel r₁ s₁ t₁ r₂ (sub s₀ (mul quotient s₁)) (sub t₀ (mul quotient t₁))

/-- The formal derivative. -/
def derivative (p : Dense) : Dense :=
  trim <| (Array.range (p.size - 1)).map fun (k : Nat) ↦ ((k + 1 : Nat) : ℚ) * p.getD (k + 1) 0

/-- The Taylor shift `p (x + h)`, by Horner's rule in `x + h`. -/
def shift (p : Dense) (h : ℚ) : Dense :=
  p.foldr (fun c acc ↦ add (mul acc #[h, 1]) #[c]) #[]

/-- The value `p (x)`, by Horner's rule. -/
def eval (p : Dense) (x : ℚ) : ℚ := p.foldr (fun c total ↦ c + x * total) 0

end Dense

end CAS.Command.Algebra
