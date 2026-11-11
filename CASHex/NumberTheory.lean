/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS
public meta import CAS
public import HexPrimalityTheory
public meta import HexPrimalityTheory
public meta import HexPrimality.Construction
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.Data.Nat.Squarefree

/-!
# Primality and factorization through Hex: `primeQ n`, `moebiusMu n`, `[factorInteger]`

With Hex (the optional build `lake -R -Khex=on build CASHex`), the calls `primeQ n`, `moebiusMu n`
and `eulerPhi n` and the mode `#cas [factorInteger] n`, as Mathematica's `PrimeQ`, `MoebiusMu`,
`EulerPhi` and `FactorInteger`, get backends registered with `@[cas_route]`
(`CAS.Tactic.RouteRegistry`). They prove `Nat.Prime n` or `¬ Nat.Prime n`,
`Nat.primeFactorsList n = [p₁, …]`, `ArithmeticFunction.moebius n = μ` and `Nat.totient n = t`.
Each backend receives the argument of its call or mode.

## Main definitions

* `primeQBackend`, `factorIntegerBackend`, `moebiusMuBackend`, `eulerPhiBackend`: the backends.
* `factorSearch`, `primeFactors?`: Hex's factor search with Hex's budgets, and the sorted prime
  factors it finds when every one passes Hex's primality test.

## Main results

* `primeFactorsList_eq_of_prod`: a sorted list of primes with product `n` is
  `Nat.primeFactorsList n`.

## Implementation notes

Hex's searches only propose. `Hex.Nat.isPrime` decides primality in compiled code, and
`Hex.Nat.Construction.factorSearch` looks for factors by trial division, Pollard's `p - 1` and
rho. The kernel checks:

* a prime by Hex's `primality` (`HexPrimalityTheory`): a recursive certificate of Pocklington
  steps, and cube-root steps of Brillhart, Lehmer and Selfridge, over a table of small primes,
  which the kernel replays and `Hex.Nat.prime_iff` transports to `Nat.Prime`;
* a composite by a factor that the search found, with `Nat.not_prime_mul`;
* a factorization `Nat.primeFactorsList n = [p₁, …]` from the product and the order of the list
  (both by `decide`) and a `primality` proof of every distinct factor, through
  `primeFactorsList_eq_of_prod`, the uniqueness of prime factorization
  (`Nat.primeFactorsList_unique`);
* `ArithmeticFunction.moebius n = μ` from that factorization
  (`Nat.squarefree_iff_nodup_primeFactorsList`, `ArithmeticFunction.moebius_apply_of_squarefree`,
  `ArithmeticFunction.moebius_eq_zero_of_not_squarefree`);
* `Nat.totient n = t` from that factorization by
  `CAS.NumberTheory.totient_eq_of_primeFactorsList`, `φ(n) = n / ∏ p * ∏ (p - 1)` over the
  distinct primes.

When a search runs out of its budget the command reports that it could not decide, and claims
nothing. The theory (prime factor lists, the Möbius function, the totient) is Mathlib's and the
certificates are Hex's.

## References

* The Lean FRO and the Hex contributors, *hex: Verified computational algebra in Lean 4*,
  release v0.10.0, 2026, <https://github.com/leanprover/hex/tree/v0.10.0>.
  We call `Hex.Nat.isPrime` and `Hex.Nat.Construction.factorSearch` (HexPrimality) and the tactic
  `primality` (HexPrimalityTheory).
* Benjamin Grégoire, Laurent Théry and Benjamin Werner, "A Computational Approach to Pocklington
  Certificates in Type Theory", in *Functional and Logic Programming (FLOPS 2006)*, Lecture Notes
  in Computer Science 3945, Springer, 2006, pp. 97-113, <https://doi.org/10.1007/11737414_8>.
  Theorem 1 (Pocklington's criterion), Theorem 2 (the cube-root criterion of Brillhart, Lehmer
  and Selfridge) and the recursive certificates of Section 2.2, the kind `primality` builds;
  Hex's primality specification cites this paper.
* The mathlib Community, "The Lean Mathematical Library", in *Proceedings of the 9th ACM SIGPLAN
  International Conference on Certified Programs and Proofs (CPP 2020)*, ACM, 2020, pp. 367-381,
  <https://doi.org/10.1145/3372885.3373824>.
-/

@[expose] public section

namespace CASHex.NumberTheory

/-- A sorted list of primes with product `n` is `Nat.primeFactorsList n`. -/
theorem primeFactorsList_eq_of_prod {n : ℕ} {l : List ℕ} (hprod : l.prod = n)
    (hprime : ∀ p ∈ l, p.Prime) (hsorted : l.SortedLE) : Nat.primeFactorsList n = l :=
  (List.Perm.eq_of_sortedLE hsorted (Nat.primeFactorsList_sorted n)
    (Nat.primeFactorsList_unique hprod hprime)).symm

theorem forall_prime_nil : ∀ p ∈ ([] : List ℕ), p.Prime := by simp

theorem forall_prime_cons {q : ℕ} {l : List ℕ} (hq : q.Prime) (hl : ∀ p ∈ l, p.Prime) :
    ∀ p ∈ q :: l, p.Prime := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · exact hq
  · exact hl p hp

end CASHex.NumberTheory

public meta section

namespace CASHex.NumberTheory

open Lean Elab Command Meta Term
open CAS.Command CAS.Command.InfoView
open CAS.Command.Algebra (natTerm proveStatement checkedEvidence)
open CAS.Command.NumberTheory (parseNat logNumber intTerm)

/-- Hex's factor search (`Hex.Nat.Construction.factorSearch`) on `n`, with the allocation of
Hex's certificate construction (`Hex.Nat.constructionBudget`) and Hex's production rho budget
(`Hex.Nat.defaultPrimeCertBudget`): claimed prime factors with exponents and the unfactored
residual. -/
def factorSearch (n : Nat) : Hex.Nat.FactorSearchResult :=
  Hex.Nat.Construction.factorSearch
    { Hex.Nat.constructionBudget.factor with primeBudget := Hex.Nat.defaultPrimeCertBudget } n
    (Hex.Rand.ofSeed n)

/-- The least nontrivial factor of a composite `n` that Hex's factor search finds. -/
def factorOf? (n : Nat) : Option Nat :=
  ((factorSearch n).raw.factors.filterMap fun (p, _) ↦
    if 1 < p && p < n && n % p = 0 then some p else none).min?

/-- The prime factors of `n ≥ 1` with multiplicity, sorted, from Hex's factor search with every
factor confirmed by Hex's primality test, or `none` when the search leaves an unfactored residual
or a factor fails the test. -/
def primeFactors? (n : Nat) : Option (List Nat) := do
  if n ≤ 1 then return []
  let result := factorSearch n
  unless result.raw.residual = 1 && result.raw.factors.all (Hex.Nat.isPrime ·.1) do none
  return (result.raw.factors.flatMap fun (p, e) ↦ List.replicate e p).mergeSort (· ≤ ·)

/-- A proof of `Nat.Prime p` by Hex's `primality`. -/
def primeProof (p : Nat) : TermElabM Lean.Expr := do
  let type ← mkAppM ``Nat.Prime #[mkNatLit p]
  let proof ← withoutErrToSorry <| elabTermEnsuringType (← `(by primality)) type
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars proof

/-- A proof of `Nat.primeFactorsList n = l` for the sorted primes `l` with product `n`. -/
def factorizationProof (n : Nat) (primes : List Nat) : TermElabM Lean.Expr := do
  let mut cache : List (Nat × Lean.Expr) := []
  for p in primes.eraseDups do
    cache := cache ++ [(p, ← primeProof p)]
  let nat := Lean.mkConst ``Nat
  let mut hprime := Lean.mkConst ``forall_prime_nil
  let mut tail : List Nat := []
  for q in primes.reverse do
    let tailE ← mkListLit nat (tail.map mkNatLit)
    let hq := (cache.find? (·.1 = q)).get!.2
    hprime := mkAppN (Lean.mkConst ``forall_prime_cons) #[mkNatLit q, tailE, hq, hprime]
    tail := q :: tail
  let l ← mkListLit nat (primes.map mkNatLit)
  let partial0 := mkAppN (Lean.mkConst ``primeFactorsList_eq_of_prod) #[mkNatLit n, l]
  let .forallE _ productType _ _ ← whnf (← inferType partial0)
    | throwError "factorInteger: internal error"
  let partial1 := mkApp partial0 (← mkDecideProof productType)
  let partial2 := mkApp partial1 hprime
  let .forallE _ sortedType _ _ ← whnf (← inferType partial2)
    | throwError "factorInteger: internal error"
  return mkApp partial2 (← mkDecideProof sortedType)

/-- `[(p, k), …]` from a sorted list with multiplicity. -/
def group (l : List Nat) : List (Nat × Nat) :=
  l.foldl (fun acc p ↦ match acc.getLast? with
    | some (q, k) => if q = p then acc.dropLast ++ [(q, k + 1)] else acc ++ [(p, 1)]
    | none => [(p, 1)]) []

/-- The text of a factorization `2^3*3^2*5`. -/
def factorizationText (pairs : List (Nat × Nat)) : String :=
  "*".intercalate (pairs.map fun (p, k) ↦ if k = 1 then s!"{p}" else s!"{p}^{k}")

/-- Run the call `primeQ n` through Hex; `input` is `n`. -/
def logPrimeQ (ref input : Syntax) : CommandElabM Unit := do
  let n ← parseNat "primeQ" input
  let (proposition, proof, answer, how) : Lean.Expr × Lean.Expr × String × String ←
    if n < 2 then
      let (a, b) ← liftTermElabM <| proveStatement "primeQ"
        (← `(¬ Nat.Prime $(natTerm n))) (← `(tactic| norm_num))
      pure (a, b, "False", "0 and 1 are not prime")
    else if Hex.Nat.isPrime n then
      let (a, b) ← liftTermElabM do
        proveStatement "primeQ" (← `(Nat.Prime $(natTerm n))) (← `(tactic| primality))
      pure (a, b, "True", "Hex primality certificate")
    else
      let some d := factorOf? n
        | throwErrorAt input "primeQ: `{Arguments.argumentText input}` is composite (Hex's test), \
            but no factor was found within the budget; nothing is claimed"
      let (a, b) ← liftTermElabM <| proveStatement "primeQ"
        (← `(¬ Nat.Prime $(natTerm n)))
        (← `(tactic| (
          rw [show ($(natTerm n) : ℕ) = $(natTerm d) * $(natTerm (n / d)) by norm_num]
          exact Nat.not_prime_mul (by norm_num) (by norm_num))))
      pure (a, b, "False", s!"{n} = {d}*{n / d}")
  logNumber ref "primeQ" s!"{n}" answer s!"primality ({how})" proposition proof

/-- Run `#cas [factorInteger] n` through Hex; `input` is `n`. -/
def logFactorInteger (ref input : Syntax) : CommandElabM Unit := do
  let n ← parseNat "factorInteger" input
  if n < 2 then throwErrorAt input "factorInteger: expected a natural number at least 2"
  let some primes := primeFactors? n
    | throwErrorAt input "factorInteger: Hex's factor search ran out of budget; nothing is claimed"
  let pairs := group primes
  let (proposition, proof) ← liftTermElabM do
    let list ← `(([$(primes.toArray.map natTerm),*] : List ℕ))
    let statement ← elabType (← `(Nat.primeFactorsList $(natTerm n) = $list))
    synthesizeSyntheticMVarsNoPostponing
    let statement ← instantiateMVars statement
    let proof ← factorizationProof n primes
    return (statement, ← mkExpectedTypeHint proof statement)
  logNumber ref "factorInteger" s!"{n}" s!"{factorizationText pairs}  {pairs}"
    "prime factorization" proposition proof

/-- Run the call `moebiusMu n` through Hex; `input` is `n`. -/
def logMoebius (ref input : Syntax) : CommandElabM Unit := do
  let n ← parseNat "moebiusMu" input
  if n = 0 then throwErrorAt input "moebiusMu: expected a positive natural number"
  let some primes := primeFactors? n
    | throwErrorAt input "moebiusMu: Hex's factor search ran out of budget; nothing is claimed"
  let squarefree := primes.eraseDups.length == primes.length
  let μ : Int := if squarefree then (-1) ^ primes.length else 0
  let (proposition, proof) ← liftTermElabM do
    let hT ← Term.exprToSyntax (← factorizationProof n primes)
    let nT := natTerm n
    let statement ← `(ArithmeticFunction.moebius $nT = $(← intTerm μ))
    if squarefree then
      proveStatement "moebiusMu" statement (← `(tactic| (
        have hf : Nat.primeFactorsList $nT = _ := $hT
        rw [ArithmeticFunction.moebius_apply_of_squarefree
            ((Nat.squarefree_iff_nodup_primeFactorsList (by norm_num)).mpr
              (by rw [hf]; decide +kernel)),
          ArithmeticFunction.cardFactors_apply, hf]
        norm_num)))
    else
      proveStatement "moebiusMu" statement (← `(tactic| (
        have hf : Nat.primeFactorsList $nT = _ := $hT
        exact ArithmeticFunction.moebius_eq_zero_of_not_squarefree fun h ↦ by
          have := (Nat.squarefree_iff_nodup_primeFactorsList (by norm_num)).mp h
          rw [hf] at this
          exact absurd this (by decide +kernel))))
  logNumber ref "moebiusMu" s!"{n}" s!"{μ}" "Möbius function" proposition proof

/-- Run the call `eulerPhi n` through Hex, for `n ≥ 2`: `φ(n) = n / ∏ p * ∏ (p - 1)` over the
distinct primes `p` of Hex's factorization. -/
def logEulerPhi (ref input : Syntax) : CommandElabM Unit := do
  let n ← parseNat "eulerPhi" input
  if n < 2 then throwErrorAt input "eulerPhi: internal error"
  let some primes := primeFactors? n
    | throwErrorAt input "eulerPhi: Hex's factor search ran out of budget; nothing is claimed"
  let distinct := primes.eraseDups
  let t := n / distinct.prod * (distinct.map (· - 1)).prod
  let (proposition, proof) ← liftTermElabM do
    let hT ← Term.exprToSyntax (← factorizationProof n primes)
    let nT := natTerm n
    let sT ← `(([$(distinct.toArray.map natTerm),*] : List ℕ))
    proveStatement "eulerPhi" (← `(Nat.totient $nT = $(natTerm t))) (← `(tactic| (
      have hf : Nat.primeFactorsList $nT = _ := $hT
      exact (CAS.NumberTheory.totient_eq_of_primeFactorsList (s := $sT) hf
        (by decide +kernel)).trans (by decide +kernel))))
  logNumber ref "eulerPhi" s!"{n}" s!"{t}" "eulerPhi" proposition proof

/-- The call `primeQ n` through Hex, as the backend registered under `primeQ`; `stx` is `n`. -/
@[cas_route primeQ]
def primeQBackend : CAS.Tactic.RouteRegistry.CommandBackend := fun stx ↦ do
  logPrimeQ stx stx
  return true

/-- `#cas [factorInteger] n` through Hex, as the backend registered under `factorInteger`; `stx`
is `n`. -/
@[cas_route factorInteger]
def factorIntegerBackend : CAS.Tactic.RouteRegistry.CommandBackend := fun stx ↦ do
  logFactorInteger stx stx
  return true

/-- The call `moebiusMu n` through Hex, as the backend registered under `moebiusMu`; `stx` is
`n`. -/
@[cas_route moebiusMu]
def moebiusMuBackend : CAS.Tactic.RouteRegistry.CommandBackend := fun stx ↦ do
  logMoebius stx stx
  return true

/-- The call `eulerPhi n` through Hex for `n ≥ 2`, as the backend registered under `eulerPhi`;
`stx` is `n`. -/
@[cas_route eulerPhi]
def eulerPhiBackend : CAS.Tactic.RouteRegistry.CommandBackend := fun stx ↦ do
  logEulerPhi stx stx
  return true

end CASHex.NumberTheory
