/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.NumberTheory.Basic
public import CAS.NumberTheory.Congruence
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Data.Nat.ModEq

/-!
# Modular arithmetic: powers, inverses, the Chinese remainder theorem, Bézout coefficients

The calls `powerMod a b m` and `modularInverse a m` and the modes `chineseRemainder` and
`extendedGCD` follow Mathematica's `PowerMod`, `ModularInverse`, `ChineseRemainder` and
`ExtendedGCD` (the Jacobi symbol is in `CAS.Command.NumberTheory.Jacobi`):

* `powerMod a b m` proves `a ^ b % m = r` by `Mathlib.Meta.NormNum.evalNatPowMod`, repeated
  squaring, so exponents with hundreds of digits are fine;
* `modularInverse a m` proves `(a : ZMod m) * r = 1 ∧ (a : ZMod m)⁻¹ = r`, or
  `Nat.gcd |a| m = g ∧ ¬ IsUnit (a : ZMod m)` when there is none;
* `chineseRemainder ([r₁, …], [m₁, …])` proves `x < M` and that `y ≡ rᵢ [MOD mᵢ]` for all `i`
  exactly when `y ≡ x [MOD M]`, for the lcm `M` of the moduli
  (`CAS.NumberTheory.modEq_iff_of_lcm`), and `¬ ∃ y, …` when two congruences disagree
  (`CAS.NumberTheory.not_exists_of_incompatible`);
* `extendedGCD (a, b)` proves `Nat.gcd a b = g ∧ a * s + b * t = g` in `ℤ`.

## Implementation notes

Finite facts about numerals are decided by kernel evaluation. We state the inverse in `ZMod m`,
where Mathlib's `⁻¹` lives, so a proof can rewrite with it; the kernel computes in `ZMod m` as in
`Fin m`. The Chinese remainder theorem first asked for pairwise coprime moduli. We merge the
congruences with the gcds of their moduli instead, so every compatible system gets its solution
modulo the lcm and every other one a proof that it has none.

The search is `extendedGcd`, the extended Euclidean algorithm, run outside the kernel: it gives
the Bézout coefficients of `extendedGCD`, the inverse of `modularInverse` and the merge steps of
`chineseRemainder`, where `x ≡ a (mod N)` and `x ≡ r (mod m)` become `x ≡ a + N k (mod N m / g)`
with `g = gcd N m = N s + m t` and `k = (r - a) / g * s`. The kernel decides by `decide +kernel`
the gcd, the product `a * r = 1` in `ZMod m`, and the hypotheses of
`CAS.NumberTheory.modEq_iff_of_lcm` (the lcm and the congruences of `x`) or of
`CAS.NumberTheory.not_exists_of_incompatible` (two of the pairs, whose residues differ modulo
the gcd of their moduli); `norm_num` checks the Bézout equation. Both theorems are in
`CAS/NumberTheory/Congruence.lean`, and `CAS.NumberTheory.pow_mod_eq_of_nat_mod` of
`CAS/NumberTheory/ModularPower.lean` restates the proof of `evalNatPowMod` as `a ^ b % m = r`.

The arguments of the calls `powerMod` and `modularInverse` have at most `10000` digits, and the
handlers form no number larger than an argument before the proofs. Two proofs form larger ones.
`evalNatPowMod`, which builds the proof of `powerMod`, multiplies two residues below `m`, or a
residue and the base `a`, before it reduces modulo `m`, in the meta code and in the kernel; these
products are below `m * max m a`, so they have at most `20000` digits. The kernel's check of
`a * r = 1` in `ZMod m` multiplies two residues, a number below `m ^ 2`.
-/

public meta section

namespace CAS.Command.NumberTheory

open Lean Elab Command Meta Term
open CAS.Command.InfoView
open CAS.Command.Algebra (natTerm proveStatement checkedEvidence)

/-- Report a number-theoretic result. -/
def logNumber (ref : Syntax) (operation input output outputType : String)
    (proposition proof : Lean.Expr) (domain : String := "ℕ")
    (inputType : String := "natural numbers") : CommandElabM Unit := do
  logReport ref {
    domain := domain
    input := input
    inputType := inputType
    output := output
    outputType := outputType
  } #[← liftTermElabM <| checkedEvidence operation outputType proposition proof]

/-- Run the call `powerMod a b m` on its evaluated arguments; `input` is the call. -/
def logPowerMod (ref : Syntax) (a b m : Nat) (input : Syntax) : CommandElabM Unit := do
  if m = 0 then throwErrorAt input "powerMod: the modulus must be positive"
  let (r, proof) := powModProof a b m
  let proof := mkApp5 (Lean.mkConst ``CAS.NumberTheory.pow_mod_eq_of_nat_mod) (raw a) (raw b)
    (raw m) (raw r) proof
  -- The statement has the raw literals of the proof: comparing `2 ^ b` written with `OfNat`
  -- numerals against the proof's raw literals would make the kernel evaluate the power.
  let (proposition, proof) ← liftTermElabM do
    let statement ← mkEq (← mkAppM ``HMod.hMod #[← mkAppM ``HPow.hPow #[raw a, raw b], raw m])
      (raw r)
    return (statement, ← mkExpectedTypeHint proof statement)
  logNumber ref "powerMod" s!"{a}^{b} mod {m}" s!"{r}" "modular power" proposition proof

/-- `(g, s, t)` with `a s + b t = g = gcd a b`. -/
partial def extendedGcd (a b : Int) : Int × Int × Int :=
  if b = 0 then (a, 1, 0) else
  let (g, s, t) := extendedGcd b (a % b)
  (g, t, s - (a / b) * t)

/-- An integer as term syntax. -/
def intTerm {m : Type → Type} [Monad m] [MonadQuotation m] (z : Int) : m (TSyntax `term) :=
  if z < 0 then `(-$(natTerm z.natAbs)) else pure (natTerm z.toNat)

/-- Run the call `modularInverse a m` on its evaluated arguments; `input` is the call. -/
def logModularInverse (ref : Syntax) (a : Int) (m : Nat) (input : Syntax) :
    CommandElabM Unit := do
  if m < 2 then throwErrorAt input "modularInverse: the modulus must be at least 2"
  -- The residue `0 ≤ a % m < m` has the same gcd with `m` and the same inverse as `a`. As for
  -- the Bézout coefficients of Euclid's algorithm, every coefficient and every product
  -- `(x / y) * t` that `extendedGcd residue m` forms is at most `m` in absolute value.
  let residue := (a % m).toNat
  let (g, s, _) := extendedGcd residue m
  let mT := natTerm m
  let (proposition, proof, output, outputType) ← liftTermElabM do
    let aT ← `(($(← intTerm a) : ZMod $mT))
    if g ≠ 1 then
      let (p, q) ← proveStatement "modularInverse"
        (← `(Nat.gcd $(natTerm a.natAbs) $mT = $(natTerm g.toNat) ∧ ¬ IsUnit $aT))
        (← `(tactic| (
          refine ⟨by decide +kernel, ?_⟩
          rw [show $aT = (($(natTerm residue) : ℕ) : ZMod $mT) by decide +kernel,
            ZMod.isUnit_iff_coprime]
          decide +kernel)))
      return (p, q, s!"none: gcd = {g}", "no inverse")
    -- `Int.emod` by `m ≥ 2` lies in `[0, m)`, so `s % m` is the residue itself.
    let r := (s % m).toNat
    let (p, q) ← proveStatement "modularInverse"
      (← `($aT * $(natTerm r) = 1 ∧ $aT⁻¹ = $(natTerm r)))
      (← `(tactic| exact ⟨by decide +kernel,
        ZMod.inv_eq_of_mul_eq_one $mT $aT $(natTerm r) (by decide +kernel)⟩))
    return (p, q, s!"{r}", "modular inverse")
  logNumber ref "modularInverse" s!"{a} mod {m}" output outputType proposition proof
    (domain := s!"ZMod {m}") (inputType := "integer and modulus")

/-- Run `#cas [extendedGCD] (a, b)`. -/
def logExtendedGCD (ref input : Syntax) : CommandElabM Unit := do
  let args ← parseNatTuple "extendedGCD" input
  let #[a, b] := args | throwErrorAt input "extendedGCD: expected `(a, b)`"
  let (g, s, t) := extendedGcd a b
  let (proposition, proof) ← liftTermElabM <| proveStatement "extendedGCD"
    (← `(Nat.gcd $(natTerm a) $(natTerm b) = $(natTerm g.toNat) ∧
      ($(natTerm a) : ℤ) * $(← intTerm s) + ($(natTerm b) : ℤ) * $(← intTerm t) =
        $(natTerm g.toNat)))
    (← `(tactic| exact ⟨by decide +kernel, by norm_num⟩))
  logNumber ref "extendedGCD" s!"({a}, {b})" s!"{g}, [{s}, {t}]" "gcd and Bézout coefficients"
    proposition proof

/-- Read a list `[a, b, …]` of natural numbers. -/
def parseNatList (operation : String) (stx : Syntax) : CommandElabM (Array Nat) := do
  match stx with
  | `([$entries,*]) => entries.getElems.mapM (parseNat operation ·)
  | _ => throwErrorAt stx "{operation}: expected a list `[a, b, …]`"

/-- Run `#cas [chineseRemainder] ([r₁, …], [m₁, …])`. -/
def logChineseRemainder (ref input : Syntax) : CommandElabM Unit := do
  let (rs, ms) ← match input with
    | `(($rs, $ms)) => pure (← parseNatList "chineseRemainder" rs,
        ← parseNatList "chineseRemainder" ms)
    | _ => throwErrorAt input "chineseRemainder: expected `([r₁, r₂, …], [m₁, m₂, …])`"
  unless rs.size = ms.size && rs.size > 0 do
    throwErrorAt input "chineseRemainder: expected as many residues as moduli"
  unless ms.all (· > 0) do throwErrorAt input "chineseRemainder: the moduli must be positive"
  let pairs := (ms.zip rs).toList
  let shown := ", ".intercalate (pairs.map fun (m, r) ↦ s!"x ≡ {r} mod {m}")
  let pairsT ← liftTermElabM do
    `(([$(← pairs.toArray.mapM fun (m, r) ↦ `(($(natTerm m), $(natTerm r)))),*] : List (ℕ × ℕ)))
  let y := mkIdent `y
  -- `x ≡ rᵢ (mod mᵢ)` and `x ≡ rⱼ (mod mⱼ)` have a common solution exactly when
  -- `rᵢ ≡ rⱼ (mod gcd mᵢ mⱼ)`, and a system has one when all its pairs do.
  for i in [0:ms.size] do
    for j in [i + 1:ms.size] do
      let g := Nat.gcd ms[i]! ms[j]!
      unless rs[i]! % g = rs[j]! % g do
        let (proposition, proof) ← liftTermElabM <| proveStatement "chineseRemainder"
          (← `(¬ ∃ $y:ident : ℕ, ∀ p ∈ $pairsT, $y ≡ p.2 [MOD p.1]))
          (← `(tactic| exact CAS.NumberTheory.not_exists_of_incompatible
            (m₁ := $(natTerm ms[i]!)) (r₁ := $(natTerm rs[i]!)) (m₂ := $(natTerm ms[j]!))
            (r₂ := $(natTerm rs[j]!)) (by decide +kernel) (by decide +kernel)
            (by decide +kernel)))
        logNumber ref "chineseRemainder" shown
          s!"none: x ≡ {rs[i]!} mod {ms[i]!} and x ≡ {rs[j]!} mod {ms[j]!} disagree modulo {g}"
          "no solution" proposition proof
        return
  -- Merge the congruences one at a time: `x ≡ a (mod N)` and `x ≡ r (mod m)` give
  -- `x ≡ a + N k (mod N m / g)` with `g = gcd N m = N s + m t` and `k = (r - a) / g * s`.
  let (x, M) := pairs.foldl (fun (a, N) (m, r) ↦
    let (g, s, _) := extendedGcd N m
    let step := m / g.toNat
    let k := (((r : Int) - a) / g * s % step + step) % step
    let L := N * step
    ((((a : Int) + N * k) % L + L) % L |>.toNat, L)) ((0 : Nat), (1 : Nat))
  let (proposition, proof) ← liftTermElabM <| proveStatement "chineseRemainder"
    (← `($(natTerm x) < $(natTerm M) ∧ ∀ $y:ident : ℕ,
      (∀ p ∈ $pairsT, $y ≡ p.2 [MOD p.1]) ↔ $y ≡ $(natTerm x) [MOD $(natTerm M)]))
    (← `(tactic| exact ⟨by decide +kernel, CAS.NumberTheory.modEq_iff_of_lcm
      $pairsT $(natTerm x) $(natTerm M) (by decide +kernel) (by decide +kernel)⟩))
  logNumber ref "chineseRemainder" shown s!"{x} mod {M}" "all solutions" proposition proof

end CAS.Command.NumberTheory

namespace CAS.Command

open Lean Elab Command

/-- `#cas [chineseRemainder] ([r₁, …, rₖ], [m₁, …, mₖ])` solves the congruences `x ≡ rᵢ (mod mᵢ)`
and proves that `x mod M`, with `M = lcm(m₁, …, mₖ)`, gives all solutions, or that there are none.

## Theorem
The report proves `x < M ∧ ∀ y : ℕ, (∀ p ∈ [(m₁, r₁), …], y ≡ p.2 [MOD p.1]) ↔ y ≡ x [MOD M]`
with Mathlib's `Nat.ModEq`, by `CAS.NumberTheory.modEq_iff_of_lcm`; kernel evaluation decides
`x < M`, the lcm and the congruences of `x`. When two congruences disagree modulo the gcd of
their moduli, it proves `¬ ∃ y : ℕ, ∀ p ∈ [(m₁, r₁), …], y ≡ p.2 [MOD p.1]` by
`CAS.NumberTheory.not_exists_of_incompatible` and prints the two.

## Conditions and limits
The residues and the moduli are natural numbers, literals or closed integer expressions, as many
residues as moduli and at least one of each. The moduli are positive; they need not be coprime.
A residue may exceed its modulus.

## Options
None.

## Examples
```lean
#cas [chineseRemainder] ([2, 3, 2], [3, 5, 7])
```
```output
Output (all solutions): 23 mod 105
```
```lean
#cas [chineseRemainder] ([2, 4], [4, 6])
```
```output
Output (all solutions): 10 mod 12
```
```lean
#cas [chineseRemainder] ([1, 2], [4, 6])
```
```output
Output (no solution): none: x ≡ 1 mod 4 and x ≡ 2 mod 6 disagree modulo 2
```
```lean
#cas [chineseRemainder] ([5], [3])
```
```output
Output (all solutions): 2 mod 3
```

## In a proof
```lean
theorem sunzi_next
    (h : 23 < 105 ∧ ∀ y : ℕ, (∀ p ∈ ([(3, 2), (5, 3), (7, 2)] : List (ℕ × ℕ)),
      y ≡ p.2 [MOD p.1]) ↔ y ≡ 23 [MOD 105]) :
    ∀ p ∈ ([(3, 2), (5, 3), (7, 2)] : List (ℕ × ℕ)), 128 ≡ p.2 [MOD p.1] :=
  (h.2 128).2 (by decide)
```
A proof can take the printed theorem as a hypothesis and use the equivalence, as here for the
next solution `128 = 23 + 105`.

## See also
Mathematica `ChineseRemainder`, SymPy `crt`. The mode `extendedGCD` and the call
`modularInverse a m`.

## Possible issues
```lean
#cas [chineseRemainder] ([2, 3], [3, 5, 7])
```
```output
chineseRemainder: expected as many residues as moduli
```
Each modulus needs its residue, and the residues come first.
-/
syntax (name := casChineseRemainderCommand) "#cas" "[" &"chineseRemainder" "]" term : command

/-- `#cas [extendedGCD] (a, b)` computes `g = gcd(a, b)` and Bézout coefficients `s` and `t` with
`a s + b t = g`, and proves both facts.

## Theorem
The report proves `Nat.gcd a b = g ∧ a * s + b * t = g`, the second equation in `ℤ`. The
coefficients come from the extended Euclidean algorithm; kernel evaluation decides the gcd and
`norm_num` the equation. The report prints `g, [s, t]`, as Mathematica's `ExtendedGCD`.

## Conditions and limits
`a` and `b` are natural numbers, literals or closed integer expressions; `s` and `t` are
integers.

## Options
None.

## Examples
```lean
#cas [extendedGCD] (240, 46)
```
```output
Output (gcd and Bézout coefficients): 2, [-9, 47]
```
```lean
#cas [extendedGCD] (17, 3120)
```
```output
Output (gcd and Bézout coefficients): 1, [-367, 2]
```

## In a proof
```lean
theorem bezout_240_46 : Nat.gcd 240 46 = 2 ∧ (240 : ℤ) * (-9) + 46 * 47 = 2 := by
  cas
```

## See also
Mathematica `ExtendedGCD`, SymPy `igcdex`. The mode `chineseRemainder`, the call
`modularInverse a m` and the mode `polynomialGCD`.

## Possible issues
```lean
#cas [extendedGCD] (-240, 46)
```
```output
extendedGCD: expected a natural number
```
The arguments are natural numbers. Since `gcd(-a, b) = gcd(a, b)`, the coefficients for `-a`
are those for `a` with the sign of `s` reversed.
-/
syntax (name := casExtendedGCDCommand) "#cas" "[" &"extendedGCD" "]" term : command

elab_rules : command
  | `(#cas [chineseRemainder] $e:term) => NumberTheory.logChineseRemainder e e
  | `(#cas [extendedGCD] $e:term) => NumberTheory.logExtendedGCD e e

end CAS.Command
