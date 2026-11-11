/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Command.NumberTheory.Basic
public meta import CAS.Tactic.RouteRegistry

/-!
# Primality and factorization through Hex

The calls `primeQ n` and `moebiusMu n` and the mode `#cas [factorInteger] n` follow
Mathematica's `PrimeQ`, `MoebiusMu` and `FactorInteger`. Primality certificates and integer
factorization are Hex's (the Lean FRO's verified computer algebra), so SymLean does not implement
them: `CASHex.NumberTheory` registers their backends, which call Hex and check its certificates.
Without Hex they refuse. The same module gives the call `eulerPhi n` Hex's factorization.

## Main definitions

* `CAS.Command.NumberTheory.runHexBackend`: run the backend of a function on its argument, or
  refuse.

## Implementation notes

`runHexBackend` asks `CAS.Tactic.RouteRegistry.runCommandBackends` for a backend registered
under the name of the call or mode, and refuses with the build instructions when there is none.
The backends are in `CASHex/NumberTheory.lean`. A prime is proved by Hex's `primality`, a
Pocklington certificate that the kernel replays, and a factorization by
`CASHex.NumberTheory.primeFactorsList_eq_of_prod` from the product of the factors, a primality
certificate for each factor and the order of the list; Hex's factor search
(`Hex.Nat.Construction.factorSearch`) only proposes the factors. The syntax of
`[factorInteger]` is declared here, in the main library, so that without Hex the mode refuses
with these instructions.
-/

public meta section

namespace CAS.Command

open Lean Elab Command

/-- `#cas [factorInteger] n` computes the prime factorization of a natural number `n ≥ 2` with Hex
and proves it. The mode needs Hex: it runs after `import CASHex.NumberTheory` in a build with
`-Khex=on`.

## Theorem
The report proves `Nat.primeFactorsList n = [p₁, …, pₖ]`, Mathlib's list of the prime factors of
`n` with multiplicity in increasing order. Hex's factor search (trial division, Pollard's `p - 1`
and rho) proposes the factors. The kernel checks that their product is `n` and that the list is
sorted, and replays Hex's primality certificate of each factor; the uniqueness of prime
factorization then gives the list (`CASHex.NumberTheory.primeFactorsList_eq_of_prod`). The report
prints the product `p₁^e₁*⋯` and the pairs `(p, e)`, as Mathematica's `FactorInteger`.

## Conditions and limits
`n` is a natural number with `n ≥ 2`, a literal or a closed integer expression. When Hex's
factor search runs out of budget, the command refuses and claims nothing. Without Hex the command
refuses.

## Options
None.

## Examples
```lean
#cas [factorInteger] 600851475143
```
```output
Output (prime factorization): 71*839*1471*6857  [(71, 1), (839, 1), (1471, 1), (6857, 1)]
```
```lean
#cas [factorInteger] 1000000016000000063
```
```output
Output (prime factorization): 1000000007*1000000009  [(1000000007, 1), (1000000009, 1)]
```
```lean
#cas [factorInteger] 2305843009213693953
```
```output
Output (prime factorization): 3*768614336404564651  [(3, 1), (768614336404564651, 1)]
```

## In a proof
```lean
theorem largest_prime_factor
    (h : Nat.primeFactorsList 600851475143 = [71, 839, 1471, 6857]) :
    ∀ p ∈ Nat.primeFactorsList 600851475143, p ≤ 6857 := by
  rw [h]
  decide
```
A proof can take the printed theorem as a hypothesis and read the factors off the list, as here
the largest one.

## See also
Mathematica `FactorInteger`, SymPy `factorint`, Hex `Hex.Nat.Construction.factorSearch` and the
`primality` certificates of `HexPrimalityTheory` (through `CASHex.NumberTheory`). The calls
`primeQ n` and `moebiusMu n`, and the modes `divisors` and `factor`, which factors polynomials.

## Possible issues
```lean
#cas [factorInteger] 360
```
```output
factorInteger needs Hex (`-Khex=on`): primality certificates and integer factorization come from
Hex; build with `lake -R -Khex=on build CASHex` and `import CASHex.NumberTheory`
```
Without Hex the mode refuses. Build Hex with `lake -R -Khex=on build CASHex` and add
`import CASHex.NumberTheory`; `#cas [divisors] n` lists the divisors of `n < 10^12` without Hex.
```lean
#cas [factorInteger] 1
```
```output
factorInteger: expected a natural number at least 2
```
`1` has no prime factors: `Nat.primeFactorsList 1 = []`.
-/
syntax (name := casFactorIntegerCommand) "#cas" "[" &"factorInteger" "]" term : command

/-- Run the backend registered under `operation` on the argument `input` of the call or mode
`operation`, or refuse at `input` when none is registered, since `operation` needs Hex. -/
def NumberTheory.runHexBackend (operation : Name) (input : Syntax) : CommandElabM Unit := do
  unless ← Tactic.RouteRegistry.runCommandBackends operation input do
    throwErrorAt input "{operation} needs Hex (`-Khex=on`): primality certificates and integer \
      factorization come from Hex; build with `lake -R -Khex=on build CASHex` and \
      `import CASHex.NumberTheory`"

elab_rules : command
  | `(#cas [factorInteger] $n:term) => NumberTheory.runHexBackend `factorInteger n

end CAS.Command
