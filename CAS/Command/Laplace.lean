/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.Algebra.Basic
public import CAS.Command.ParamSystems
public import CAS.Command.Integration
public import CAS.Command.Series
public import CAS.Calculus.ConditionFree
public import CAS.Calculus.ExpTrigPrimitive
public import CAS.Calculus.Laplace
public meta import CAS.Calculus.ConditionFree
public meta import CAS.Integration.ExponentialTrig

/-!
# Laplace transforms: `#cas [laplace t s] f`

`#cas [laplace t s] f` (Mathematica's `LaplaceTransform[f, t, s]`) for `f` a sum of terms
`c tⁿ e ^ (a t) g (b t)` with `g` one of `1`, `cos`, `sin`, `cosh`, `sinh` and rational `a`, `b`,
`c` (the exponential and `g` may be missing) proves

`∀ s : ℝ, σ < s → IntegrableOn (fun t ↦ exp (-(s t)) f t) (Ioi 0) ∧
  ∫ t in Ioi 0, exp (-(s t)) f t = F`

with `σ` the largest bound of a term with a coefficient `≠ 0` (terms with coefficient `0` are
dropped first; `σ = 0` if none is left), `a` for `1`, `cos`, `sin` and `a + |b|` for `cosh`,
`sinh` (sufficient, not always optimal: `cosh t - sinh t` gets `σ = 1`), and `F` an explicit sum
of rational functions of `s`, one per term, with `u = s - a`: `c n! / u ^ (n + 1)`,
`c n! P (u) / (u ^ 2 + b ^ 2) ^ (n + 1)` with `P` the real or imaginary part of
`(u + b i) ^ (n + 1)` for `cos`, `sin`, and `c n! P (u) / (u ^ 2 - b ^ 2) ^ (n + 1)` with `P` the
part of `(u + b) ^ (n + 1)` of even (`cosh`) or odd (`sinh`) degree in `b`. The integrand in the
theorem is the input as written (elaborated over `ℝ` with `Real` open).

Refused: symbolic parameters, frequencies `b = 0`, `tanh`, inputs inside a section with
`variable`s (the statement is elaborated without them), powers `n > 8`, more than 8 terms
(counted after dropping terms with coefficient `0`), constant powers and decimal literals with
an exponent over 256 (under the default `exponentiation.threshold` of 256, `norm_num` and `ring`
can leave such powers unevaluated, and the proof of an accepted input may fail; the threshold
itself is read from the options when the proof runs, the limit here is fixed). Resource limits,
checked before the work they bound: a weighted syntax budget of 600 (`inputSize`: syntax nodes,
the arguments of `sinh`, `cosh` and `tan` weighted twice, as the shared reader copies them), no
literal of more than 320 characters, and every rational constant read from the input (literals
and the results of `+ - * /` and `^`) has a numerator and a denominator of at most 1024 bits.

## Implementation notes

The transforms are proved in `CAS/Calculus/Laplace.lean`, not here. There we show
`∫₀^∞ tⁿ e^(-w t) dt = n! / w^(n+1)` for a complex rate `w`
(`integral_pow_mul_cexp_neg_mul_Ioi`) and take real and imaginary parts for `cos` and `sin`
(`laplacePQ`), and `integral_exp_mul_sum` is linearity over a list of `LaplaceTerm`s. The command
reads the terms with `hterms?`, the reader `CAS.IntegrationPlanner.ExponentialTrig.terms?` of
`CAS/Integration/ExponentialTrig.lean` extended by `cosh` and `sinh`, which the shared reader
writes as `(e ^ u ± e ^ (-u)) / 2`, and computes each piece of `F` from the rational data in meta
code (`pq` and `hpq` give the polynomials `P`). None of this is trusted: the kernel checks
`integral_exp_mul_sum` applied to the literal list of terms, the admissibility of each term for
`σ < s` (`linarith`), the equality of the input with the sum of the terms (`simp` with
`Real.cosh_eq`, `Real.sinh_eq`, then `ring_nf`), and one equation per term between
`LaplaceTerm.transform` and its piece of `F` (`simp`, `field_simp`, `ring`).

We prove the pieces one at a time, since a single `field_simp` over the whole sum would clear
every denominator at once. For `cosh` and `sinh` the library's transform is `c n! / 2` times
`1 / (u - b) ^ (n + 1) ± 1 / (u + b) ^ (n + 1)`. We combine the two fractions over
`(u ^ 2 - b ^ 2) ^ (n + 1)` with `div_add_div` or `div_sub_div` and then generalize
`u ^ 2 - b ^ 2` to one atom, so that `field_simp` sees a single nonzero denominator. The table
of transforms is classical; the reader, the bound `σ` and the proof script are ours.
-/

public meta section

namespace CAS.Command.Laplace

open Lean Elab Command Meta Term
open CAS.Command.InfoView
open CAS.IntegrationPlanner.ExponentialTrig

/-- The largest power `n` of `t` in a term. -/
def maxPower : Nat := 8

/-- The largest number of terms. -/
def maxTerms : Nat := 8

/-- A bound on the size in bits of the numerator and of the denominator of every rational constant
read from the input: literals, sums, differences, products, quotients and powers. -/
def maxBits : Nat := 1024

/-- The weighted syntax budget of the input, see `inputSize`. -/
def maxSize : Nat := 600

/-- A bound on the length of a literal of the input (`10 ^ 320 > 2 ^ maxBits`), checked before the
shared reader decodes it. -/
def maxLiteral : Nat := 320

/-- The largest exponent of a constant power and the largest power of ten of a decimal literal:
Lean's default `exponentiation.threshold`, above which `norm_num` and `ring` can leave a power
unevaluated. -/
def maxExponent : Nat := 256

/-- `q` if its numerator and denominator have at most `maxBits` bits (a comparison, linear in the
size of `q`), else `none`. -/
def capped (q : ℚ) : Option ℚ :=
  if 2 ^ maxBits ≤ q.num.natAbs || 2 ^ maxBits ≤ q.den then none else some q

/-- The rational value of a variable-free expression; `none` as soon as a literal or an
intermediate value has more than `maxBits` bits (so the rational operands supplied to arithmetic
have at most `maxBits` bits; a result is computed before its check), for a power with an exponent
over `maxExponent`, and before computing a power of more than `maxBits` bits. -/
partial def ratOf? {N : Nat} : Verified.Expr (Fin N) → Option ℚ
  | .nat n => capped n
  | .int n => capped n
  | .rat a b =>
      if b = 0 then none
      else if 2 ^ maxBits ≤ a.natAbs || 2 ^ maxBits ≤ b then none
      else capped ((a : ℚ) / b)
  | .add a b => do capped ((← ratOf? a) + (← ratOf? b))
  | .sub a b => do capped ((← ratOf? a) - (← ratOf? b))
  | .mul a b => do capped ((← ratOf? a) * (← ratOf? b))
  | .neg a => return -(← ratOf? a)
  | .div a b => do
      let d ← ratOf? b
      if d = 0 then none else capped ((← ratOf? a) / d)
  | .pow a k => do
      let q ← ratOf? a
      if k > maxExponent then none
      -- Refuse (`none`) before computing a power of more than `maxBits` bits
      -- (`k > maxBits / e` iff `e * k > maxBits`).
      if k > maxBits / (q.num.natAbs.log2 + q.den.log2 + 2) then none
      capped (q ^ k)
  | _ => none

/-- `tanh` (the shared reader writes `tanh u` with four copies of `u`). -/
def isTanh (f : Name) : Bool := f == `tanh || f == `Real.tanh

/-- `sinh`, `cosh` or `tan` (the shared reader writes them with two copies of the argument). -/
def isDoubling (f : Name) : Bool :=
  f == `sinh || f == `Real.sinh || f == `cosh || f == `Real.cosh || f == `tan || f == `Real.tan

/-- A weighted syntax budget controlling the expansion by the shared reader (`parseExact`), not a
literal bound on the size of the expression it builds: the number of syntax nodes, where the
argument of an application of `sinh`, `cosh` or `tan` counts twice and that of `tanh` four times
(the reader's applications are `f u` with `f` an identifier, a `Lean.Parser.Term.app` node).
Literals count as one node; their length is bounded separately (`hasLongAtom`). Saturates at
`maxSize + 1`, so the computation is linear in the size of `stx` also for nested applications. -/
partial def inputSize (stx : Syntax) : Nat :=
  match stx with
  | .node _ kind args =>
      let sum (xs : Array Syntax) : Nat :=
        xs.foldl (fun n x ↦ min (maxSize + 1) (n + inputSize x)) 0
      if kind == ``Lean.Parser.Term.app && args.size == 2 && args[0]!.isIdent then
        let f := args[0]!.getId
        let k := if isTanh f then 4 else if isDoubling f then 2 else 1
        min (maxSize + 1) (2 + k * sum args[1]!.getArgs)
      else min (maxSize + 1) (1 + sum args)
  | _ => 1

/-- Whether `stx` has an atom (such as a numeric literal) of more than `maxLiteral` characters. -/
partial def hasLongAtom (stx : Syntax) : Bool :=
  match stx with
  | .atom _ v => v.length > maxLiteral
  | .node _ _ args => args.any hasLongAtom
  | _ => false

/-- Whether `stx` has a decimal literal (`1e-300`, `0.5`) with a power of ten over `maxExponent`
(the reader writes it without a power, `norm_num` evaluates the power in the proof). Run after
`hasLongAtom`, so that the literals decoded here are short. -/
partial def hasLargeDecimal (stx : Syntax) : Bool :=
  match stx.isScientificLit? with
  | some (_, _, e) => e > maxExponent
  | none => stx.getArgs.any hasLargeDecimal

/-- Whether `tanh` occurs in `stx`. -/
partial def hasTanh (stx : Syntax) : Bool :=
  (stx.isIdent && isTanh stx.getId) || stx.getArgs.any hasTanh

/-- A term `c tⁿ e ^ (a t) g (b t)` with rational data. -/
structure QTerm where
  /-- The coefficient. -/
  c : ℚ
  /-- The power of `t`. -/
  n : Nat
  /-- The rate of the exponential, `0` without one. -/
  a : ℚ
  /-- The frequency, `0` without a trigonometric or hyperbolic factor. -/
  b : ℚ
  /-- `0` for `g = 1`, `1` for `cos`, `2` for `sin`, `3` for `cosh`, `4` for `sinh`. -/
  kind : Nat

/-- A term `c xᵏ e ^ (a x) g (b x)` read from the input, as `ExponentialTrig.Term` but with
`g` also `cosh` or `sinh`. -/
structure HTerm (N : Nat) where
  /-- The coefficient `c`, free of `x`. -/
  coeff : Verified.Expr (Fin N)
  /-- The power `k` of `x`. -/
  power : Nat
  /-- The rate `a` of `e ^ (a x)`; `none` without an exponential factor. -/
  rate : Option (Verified.Expr (Fin N))
  /-- The frequency `b` and the kind of `g` (`1` cos, `2` sin, `3` cosh, `4` sinh); `none`
  without such a factor. -/
  freq : Option (Verified.Expr (Fin N) × Nat)

/-- `cosh u` and `sinh u` as the shared reader writes them (`(e ^ u ± e ^ (-u)) / 2`, so also
when the input is written so): `u` with the kind, `3` for `cosh` and `4` for `sinh`. -/
def hyperbolic? {N : Nat} (ex : Verified.Expr (Fin N)) : Option (Verified.Expr (Fin N) × Nat) :=
  match ex with
  | .div (.add (.exp u) (.exp (.neg v))) (.nat 2) => if u == v then some (u, 3) else none
  | .div (.sub (.exp u) (.exp (.neg v))) (.nat 2) => if u == v then some (u, 4) else none
  | _ => none

/-- The product of two terms, with at most one exponential and one other factor. -/
def hcombine {N : Nat} (s t : HTerm N) : Option (HTerm N) := do
  let rate ← match s.rate, t.rate with
    | some _, some _ => none
    | some r, none | none, some r => some (some r)
    | none, none => some none
  let freq ← match s.freq, t.freq with
    | some _, some _ => none
    | some f, none | none, some f => some (some f)
    | none, none => some none
  return { coeff := mulCoeff s.coeff t.coeff, power := s.power + t.power, rate, freq }

/-- Read a product `c xᵏ e ^ (a x) g (b x)` (as `ExponentialTrig.term?`, and `cosh`, `sinh`). -/
partial def hterm? {N : Nat} (ex : Verified.Expr (Fin N)) : Option (HTerm N) :=
  if isFree ex then some { coeff := ex, power := 0, rate := none, freq := none } else
  if isX ex then some { coeff := .nat 1, power := 1, rate := none, freq := none } else
  match hyperbolic? ex with
  | some (u, k) => do
      let b ← linear? u
      return { coeff := .nat 1, power := 0, rate := none, freq := some (b, k) }
  | none =>
  match ex with
  | .mul a b => do hcombine (← hterm? a) (← hterm? b)
  | .neg a => do
      let t ← hterm? a
      return { t with coeff := .neg t.coeff }
  | .div a d => do
      unless isFree d do none
      let t ← hterm? a
      return { t with coeff := .div t.coeff d }
  | .pow b k => if isX b then some { coeff := .nat 1, power := k, rate := none, freq := none }
      else none
  | .exp A => do
      let a ← linear? A
      return { coeff := .nat 1, power := 0, rate := some a, freq := none }
  | .cos B => do
      let b ← linear? B
      return { coeff := .nat 1, power := 0, rate := none, freq := some (b, 1) }
  | .sin B => do
      let b ← linear? B
      return { coeff := .nat 1, power := 0, rate := none, freq := some (b, 2) }
  | _ => none

/-- Read a sum of terms (as `ExponentialTrig.terms?`, with `hterm?`), each with the flag `true`
when it is subtracted. -/
partial def hterms? {N : Nat} (ex : Verified.Expr (Fin N)) : Option (List (Bool × HTerm N)) :=
  match ex with
  | .add a b => return (← hterms? a) ++ (← hterms? b)
  | .sub a b => return (← hterms? a) ++ ((← hterms? b).map fun (s, t) ↦ (!s, t))
  | .neg a => return (← hterms? a).map fun (s, t) ↦ (!s, t)
  | .mul a b =>
      if isFree a && !isFree b then do
        return (← hterms? b).map fun (s, t) ↦ (s, { t with coeff := mulCoeff a t.coeff })
      else if isFree b && !isFree a then do
        return (← hterms? a).map fun (s, t) ↦ (s, { t with coeff := mulCoeff t.coeff b })
      else do return [(false, ← hterm? ex)]
  | _ => do return [(false, ← hterm? ex)]

/-- The rational data of a term read by `hterms?`, its sign applied; `none` when a coefficient,
rate or frequency is not a rational number, or a frequency is `0`. -/
def qterm? {N : Nat} (negative : Bool) (t : HTerm N) : Option QTerm := do
  let c ← ratOf? t.coeff
  let c := if negative then -c else c
  let a ← match t.rate with
    | some r => ratOf? r
    | none => some 0
  match t.freq with
  | none => return { c, n := t.power, a, b := 0, kind := 0 }
  | some (bE, kind) =>
      let b ← ratOf? bE
      if b = 0 then none
      return { c, n := t.power, a, b, kind }

/-- A real literal for a rational. -/
def realLit (q : ℚ) : TermElabM (TSyntax `term) := do
  let num : TSyntax `term := ⟨Syntax.mkNumLit (toString q.num.natAbs)⟩
  let den : TSyntax `term := ⟨Syntax.mkNumLit (toString q.den)⟩
  let base ← if q.den = 1 then `(($num : ℝ)) else `((($num : ℝ) / $den))
  if q < 0 then `((-$base)) else pure base

/-- `(u + b i)^m = P(u) + i Q(u)`, as coefficient lists in `u` (index = power). -/
def pq (b : ℚ) : Nat → List ℚ × List ℚ
  | 0 => ([1], [])
  | m + 1 =>
    let (P, Q) := pq b m
    let get (l : List ℚ) (i : Nat) : ℚ := l.getD i 0
    let len := m + 2
    ((List.range len).map fun i ↦ (if i = 0 then 0 else get P (i - 1)) - b * get Q i,
     (List.range len).map fun i ↦ (if i = 0 then 0 else get Q (i - 1)) + b * get P i)

/-- `(u + b)^m = P(u) + Q(u)` with `P` the terms of even degree in `b` and `Q` those of odd
degree, as coefficient lists in `u` (index = power): `P (u) = Σ C(m, i) bᵐ⁻ⁱ uⁱ` over `m - i`
even, `Q` over `m - i` odd. -/
def hpq (b : ℚ) (m : Nat) : List ℚ × List ℚ :=
  ((List.range (m + 1)).map fun i ↦ if (m - i) % 2 = 0 then (m.choose i : ℚ) * b ^ (m - i) else 0,
   (List.range (m + 1)).map fun i ↦ if (m - i) % 2 = 1 then (m.choose i : ℚ) * b ^ (m - i) else 0)

/-- `k`-th power, without `^ 1`. -/
def powSyntax (u : TSyntax `term) (k : Nat) : TermElabM (TSyntax `term) := do
  if k = 1 then pure u else `($u ^ $(⟨Syntax.mkNumLit (toString k)⟩))

/-- `|q| uⁱ` as a term (`q ≠ 0`). -/
def monoSyntax (u : TSyntax `term) (q : ℚ) (i : Nat) : TermElabM (TSyntax `term) := do
  let q := |q|
  if i = 0 then realLit q
  else if q = 1 then powSyntax u i
  else `($(← realLit q) * $(← powSyntax u i))

/-- `Σ cᵢ uⁱ` as a term, highest power first, with subtraction for negative coefficients. -/
def polySyntax (u : TSyntax `term) (cs : List ℚ) : TermElabM (TSyntax `term) := do
  let mut acc : Option (TSyntax `term) := none
  for (q, i) in cs.zipIdx.reverse do
    if q = 0 then continue
    let mono ← monoSyntax u q i
    acc := some (← match acc with
      | none => if q < 0 then `(-$mono) else pure mono
      | some a => if q < 0 then `($a - $mono) else `($a + $mono))
  match acc with
  | some a => pure a
  | none => `((0 : ℝ))

/-- `s - a`, written `s` for `a = 0` and `s + |a|` for `a < 0`. -/
def shiftSyntax (s : TSyntax `term) (a : ℚ) : TermElabM (TSyntax `term) := do
  if a = 0 then pure s
  else if a < 0 then `(($s + $(← realLit (-a))))
  else `(($s - $(← realLit a)))

/-- The closed-form transform of one term, in `s`, and whether it is subtracted. -/
def transformSyntax (s : TSyntax `term) (T : QTerm) : TermElabM (TSyntax `term × Bool) := do
  let u ← shiftSyntax s T.a
  let f : ℚ := T.c * (T.n.factorial : ℚ)
  if T.kind = 0 then
    return (← `($(← realLit |f|) / $(← powSyntax u (T.n + 1))), f < 0)
  else if T.kind ≥ 3 then
    -- `n! / 2 (1 / (u - b) ^ m ± 1 / (u + b) ^ m) = n! P (u) / (u ^ 2 - b ^ 2) ^ m` (resp. `Q`).
    let (P, Q) := hpq T.b (T.n + 1)
    let num := (if T.kind = 3 then P else Q).map (f * ·)
    let negative := num.all (· ≤ 0)
    let num := if negative then num.map (- ·) else num
    let den ← powSyntax (← `(($(← powSyntax u 2) - $(← realLit (T.b ^ 2))))) (T.n + 1)
    return (← `($(← polySyntax u num) / $den), negative)
  else
    let (P, Q) := pq T.b (T.n + 1)
    let num := (if T.kind = 1 then P else Q).map (f * ·)
    let negative := num.all (· ≤ 0)
    let num := if negative then num.map (- ·) else num
    let den ← powSyntax (← `(($(← powSyntax u 2) + $(← realLit (T.b ^ 2))))) (T.n + 1)
    return (← `($(← polySyntax u num) / $den), negative)

/-- The constructor of `LaplaceKind` for a kind. -/
def kindSyntax (k : Nat) : TermElabM (TSyntax `term) :=
  match k with
  | 0 => `(CAS.Calculus.Laplace.LaplaceKind.exp)
  | 1 => `(CAS.Calculus.Laplace.LaplaceKind.cos)
  | 2 => `(CAS.Calculus.Laplace.LaplaceKind.sin)
  | 3 => `(CAS.Calculus.Laplace.LaplaceKind.cosh)
  | _ => `(CAS.Calculus.Laplace.LaplaceKind.sinh)

/-- The bound `a` of a term, `a + |b|` for `cosh` and `sinh`. -/
def QTerm.sigma (T : QTerm) : ℚ := if T.kind ≥ 3 then T.a + |T.b| else T.a

/-- Run `#cas [laplace t s] f`. -/
def logLaplace (ref : Syntax) (t s : TSyntax `ident) (input : TSyntax `term) :
    CommandElabM Unit := do
  let shape := "laplace: expected a sum of terms c tⁿ e ^ (a t) g (b t) with g one of cos, sin, \
    cosh, sinh, or c tⁿ e ^ (a t), with rational a, b, c and b ≠ 0 (parameters are not supported)"
  if t.getId == s.getId then
    throwErrorAt s "laplace: the variables t and s must be different"
  -- `liftTermElabM` elaborates the statement without the section variables, so a section variable
  -- named like a function of the input (e.g. `exp`) would silently change its meaning.
  unless (← getScope).varDecls.isEmpty do
    throwErrorAt input "laplace is not supported in a section with `variable`s"
  -- Cheap syntactic checks before the shared reader, whose work and output grow with them.
  if hasTanh input then
    throwErrorAt input "laplace: tanh is not supported"
  if hasLongAtom input then
    throwErrorAt input "laplace: a literal has more than {maxLiteral} characters"
  if hasLargeDecimal input then
    throwErrorAt input "laplace: a decimal literal has a power of ten over {maxExponent}"
  if inputSize input > maxSize then
    throwErrorAt input "laplace: the input is too large (more than {maxSize} syntax nodes, \
      the arguments of sinh, cosh and tan counted twice)"
  let reified ← try parseExact input [t.getId] catch _ => throwErrorAt input shape
  let some ts := hterms? reified.expr | throwErrorAt input shape
  let some qs := ts.mapM fun (neg, term) ↦ qterm? neg term | throwErrorAt input shape
  -- Terms with coefficient `0` are dropped: they impose no condition on `s`.
  let qs := qs.filter (·.c ≠ 0)
  if qs.length > maxTerms then
    throwErrorAt input "laplace accepts at most {maxTerms} terms"
  if qs.any (·.n > maxPower) then
    throwErrorAt input "laplace accepts powers t ^ n with n ≤ {maxPower}"
  let σ : ℚ := qs.foldl (fun m T ↦ max m T.sigma) (qs.head?.map (·.sigma) |>.getD 0)
  let tT : TSyntax `term := ⟨t.raw⟩
  let sT : TSyntax `term := ⟨s.raw⟩
  let (proposition, proof, Fpp) ← liftTermElabM do
    let σT ← realLit σ
    let mut Fsum : Option (TSyntax `term) := none
    let mut lits : Array (TSyntax `term) := #[]
    let mut adm : Array (TSyntax `term) := #[]
    -- One equation `T.transform s = piece` per term, each proved on its own: a single
    -- `field_simp` over all the terms would clear every denominator at once.
    let mut eqs : TSyntax `tactic ← `(tactic| skip)
    let mut rws : TSyntax `tactic ← `(tactic| skip)
    for T in qs do
      let (piece, negative) ← transformSyntax sT T
      Fsum := some (← match Fsum with
        | none => if negative then `(-$piece) else pure piece
        | some a => if negative then `($a - $piece) else `($a + $piece))
      let nT : TSyntax `term := ⟨Syntax.mkNumLit (toString T.n)⟩
      let lit ← `(⟨$(← realLit T.c), $nT, $(← realLit T.a), $(← realLit T.b),
        $(← kindSyntax T.kind)⟩)
      lits := lits.push lit
      adm := adm.push (← if T.kind ≥ 3 then
          `((by simp only [CAS.Calculus.Laplace.LaplaceTerm.Admissible]
                exact ⟨by linarith, by linarith⟩))
        else `((by simp only [CAS.Calculus.Laplace.LaplaceTerm.Admissible]; linarith)))
      let u ← shiftSyntax sT T.a
      let rhs ← if negative then `(-$piece) else pure piece
      let e := mkIdent (Name.mkSimple s!"laplace_eq_{lits.size}")
      let h ← if T.kind ≥ 3 then
          -- `1 / X ^ m ± 1 / Y ^ m = (Y ^ m ± X ^ m) / (u ^ 2 - b ^ 2) ^ m` with
          -- `X = s - (a + b)`, `Y = s - (a - b)`, `X Y = u ^ 2 - b ^ 2`; then `u ^ 2 - b ^ 2` is
          -- generalized, so that `field_simp` sees one atom `D ≠ 0`.
          let A ← realLit T.a
          let B ← realLit T.b
          let B2 ← realLit (T.b ^ 2)
          let U2 ← powSyntax u 2
          let X ← `(($sT - ($A + $B)))
          let Y ← `(($sT - ($A - $B)))
          let m ← `(($nT + 1))
          let (op, combined, split) ← if T.kind = 3 then
              pure (← `((1 : ℝ) / $X ^ $m + 1 / $Y ^ $m),
                ← `(($Y ^ $m + $X ^ $m) / ($U2 - $B2) ^ $m),
                ← `(tactic| rw [div_add_div _ _ (pow_ne_zero _ hX) (pow_ne_zero _ hY)]))
            else
              pure (← `((1 : ℝ) / $X ^ $m - 1 / $Y ^ $m),
                ← `(($Y ^ $m - $X ^ $m) / ($U2 - $B2) ^ $m),
                ← `(tactic| rw [div_sub_div _ _ (pow_ne_zero _ hX) (pow_ne_zero _ hY)]))
          let fact : TSyntax `term := ⟨Syntax.mkNumLit (toString T.n.factorial)⟩
          `(tactic| have $e:ident :
              CAS.Calculus.Laplace.LaplaceTerm.transform ($lit : CAS.Calculus.Laplace.LaplaceTerm)
                $sT = $rhs := by
            have hX : $X ≠ 0 := by intro h; linarith
            have hY : $Y ≠ 0 := by intro h; linarith
            have hXY : $U2 - $B2 = $X * $Y := by ring
            have key : $op = $combined := by
              rw [hXY, mul_pow]
              $split:tactic
              ring
            have hD : $U2 - $B2 ≠ 0 := by rw [hXY]; exact mul_ne_zero hX hY
            change $(← realLit T.c) * ((Nat.factorial $nT : ℝ) / 2 * $op) = $rhs
            rw [key, show (Nat.factorial $nT : ℝ) = $fact by norm_num [Nat.factorial]]
            generalize $U2 - $B2 = D at hD ⊢
            field_simp
            ring)
        else `(tactic| have $e:ident :
            CAS.Calculus.Laplace.LaplaceTerm.transform ($lit : CAS.Calculus.Laplace.LaplaceTerm)
              $sT = $rhs := by
          have : $u ≠ 0 := by intro h; linarith
          simp [CAS.Calculus.Laplace.LaplaceTerm.transform, CAS.Calculus.Laplace.laplacePQ,
            Nat.factorial] <;> (try field_simp) <;> ring)
      eqs ← `(tactic| ($eqs; $h))
      -- `try`: a repeated term is rewritten by the first of its equal equations.
      rws ← `(tactic| ($rws; try simp only [$e:ident]))
    let F ← match Fsum with
      | some F => pure F
      | none => `((0 : ℝ))
    let mut admProof ← `((by simp : ∀ T ∈ ([] : List CAS.Calculus.Laplace.LaplaceTerm),
      T.Admissible $sT))
    for h in adm.reverse do
      admProof ← `(List.forall_mem_cons.2 ⟨$h, $admProof⟩)
    let fT ← `(open Real in ($input : ℝ))
    let statement ← `(∀ $s:ident : ℝ, $σT < $sT →
      MeasureTheory.IntegrableOn (fun $t:ident : ℝ ↦ Real.exp (-($sT * $tT)) * $fT) (Set.Ioi 0) ∧
      ∫ $t:ident in Set.Ioi 0, Real.exp (-($sT * $tT)) * $fT = $F)
    let (p, q) ← Algebra.proveStatement "laplace" statement (← `(tactic| (
      intro $s:ident hs
      have key := CAS.Calculus.Laplace.integral_exp_mul_sum [$lits,*] (s := $sT) $admProof
      have hf : (fun $t:ident : ℝ ↦ Real.exp (-($sT * $tT)) * $fT) = fun $t:ident ↦
          Real.exp (-($sT * $tT)) * (([$lits,*] : List CAS.Calculus.Laplace.LaplaceTerm).map
            fun T ↦ T.eval $tT).sum := by
        funext $t:ident
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          CAS.Calculus.Laplace.LaplaceTerm.eval, zero_mul, Real.exp_zero, mul_one,
          Real.cosh_eq, Real.sinh_eq] <;>
        ring_nf <;> (try simp only [Real.exp_zero, mul_one, one_mul]) <;> (try ring_nf)
      rw [hf]
      refine ⟨key.1, key.2.trans ?_⟩
      $eqs
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      ($rws:tactic)
      all_goals ring)))
    let Fpp ← forallTelescope p fun _ body ↦ do
      match body.getAppFnArgs with
      | (``And, #[_, eq]) => match eq.eq? with
        | some (_, _, rhs) => renderTerm rhs
        | none => return "see the statement"
      | _ => return "see the statement"
    return (p, q, Fpp)
  logReport ref {
    domain := s!"{s.getId} > {σ}"
    input := surfaceText input.raw
    inputType := "terms c tⁿ e ^ (a t) g (b t), g = 1, cos, sin, cosh, sinh"
    output := Fpp
    outputType := "Laplace transform"
  } #[← liftTermElabM <| Algebra.checkedEvidence "laplace"
    s!"Laplace transform" proposition proof]

end CAS.Command.Laplace

namespace CAS.Command

open Lean Elab Command

/-- `#cas [laplace t s] f` computes the Laplace transform of `f`, a sum of polynomial, exponential,
trigonometric and hyperbolic terms in `t`, as a rational function of `s`, and proves it for every
`s` above a bound `σ`.

## Theorem
For the printed transform `F`, the report proves that for every `s : ℝ` with `σ < s`, the
function `fun t ↦ Real.exp (-(s * t)) * f` is integrable on `Set.Ioi 0` and
`∫ t in Set.Ioi 0, Real.exp (-(s * t)) * f = F` (`CAS.Calculus.Laplace.integral_exp_mul_sum`).
`σ` is the largest bound of the terms: `a` for a term with `exp (a * t)`, `cos` or `sin`, and
`a + |b|` for a term with `cosh (b * t)` or `sinh (b * t)`. It suffices for convergence and is
not always the smallest such bound.

## Conditions and limits
`f` is a sum of at most 8 terms `c * t ^ n * exp (a * t) * g (b * t)` with `g` one of `cos`,
`sin`, `cosh` and `sinh`, or without `g`, with rational `a`, `c` and `b ≠ 0`, and `n ≤ 8`.
Symbolic parameters, `tanh` and other functions are refused. The input has at most 600 syntax
nodes (the arguments of `sinh`, `cosh` and `tan` counted twice), literals of at most 320
characters, decimal literals and constant powers with exponents up to 256, and rational
constants of at most 1024 bits.

## Options
None.

## Examples
```lean
#cas [laplace t s] (t * exp (-t))
```
```output
Output (Laplace transform): 1/(s + 1)^2
```
```lean
#cas [laplace t s] (t * sin (2 * t))
```
```output
Output (Laplace transform): 4*s/(s^2 + 4)^2
```
```lean
#cas [laplace t s] (3 * t ^ 2 * exp (2 * t) + cos (5 * t))
```
```output
Output (Laplace transform): 6/(s - 2)^3 + s/(s^2 + 25)
```

## In a proof
```lean
theorem laplace_one (s : ℝ) (hs : 0 < s) :
    ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(s * t)) * 1 = 1 / s := by
  cas
```

## See also
Mathematica `LaplaceTransform`, SymPy `laplace_transform`. The modes `inverseLaplace`,
`integrate` and `dsolve`.

## Possible issues
```lean
#cas [laplace t s] (cosh t * cos t)
```
```output
laplace: expected a sum of terms c tⁿ e ^ (a t) g (b t) with g one of cos, sin, cosh, sinh, or
c tⁿ e ^ (a t), with rational a, b, c and b ≠ 0 (parameters are not supported)
```
A product of two of the functions `g` is not one term. Write it as a sum of terms first, here
`(exp t * cos t + exp (-t) * cos t) / 2`.
```lean
#cas [laplace t s] (t ^ 9)
```
```output
laplace accepts powers t ^ n with n ≤ 8
```
The transform of `t ^ n` is `n! / s ^ (n + 1)`, which the mode proves for `n ≤ 8`.
-/
syntax (name := casLaplaceCommand) "#cas" "[" &"laplace" ident ident "]" term : command

elab_rules : command
  | `(#cas [laplace $t:ident $s:ident] $f:term) => do
      Laplace.logLaplace (← getRef) t s f

end CAS.Command
