/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.Nat.Basic

/-!
# Modular powers stated through `Nat.mod (Nat.pow a b) m`

`Mathlib.Meta.NormNum.evalNatPowMod` proves `Nat.mod (Nat.pow a b) m = c` for raw literals by
repeated squaring. These lemmas restate such a proof as `a ^ b % m = c`, through hypotheses whose
statements are exactly the ones the proof has, so that neither the elaborator nor the kernel
compares `a ^ b` with `Nat.pow a b` by evaluating the power (the kernel evaluates a power with
GMP only when its exponent is small). The call `powerMod a b m` uses `pow_mod_eq_of_nat_mod`,
and bare `cas` on a goal `a ^ b % m = r` uses `pow_mod_eq_of_eq`.

## References

* The mathlib Community, "The Lean Mathematical Library", in *Proceedings of the 9th ACM SIGPLAN
  International Conference on Certified Programs and Proofs (CPP 2020)*, ACM, 2020, pp. 367-381,
  <https://doi.org/10.1145/3372885.3373824>.
  For `Mathlib.Meta.NormNum.evalNatPowMod`.
-/

@[expose] public section

namespace CAS.NumberTheory

/-- `a ^ b % m = r` from the form `Nat.mod (Nat.pow a b) m = r` of `evalNatPowMod`. Stating it
through this lemma keeps the kernel from comparing `a ^ b % m` with `Nat.mod (Nat.pow a b) m` for
numerals, which would make it evaluate the power. -/
theorem pow_mod_eq_of_nat_mod {a b m r : ℕ} (h : Nat.mod (Nat.pow a b) m = r) : a ^ b % m = r :=
  h

/-- `a ^ b % m = r` from `Nat.mod (Nat.pow a' b') m' = r'` and numeral equalities `a = a'`, …:
closing a goal written with numerals by a proof written with raw literals through this lemma
keeps the elaborator and the kernel from comparing the two powers by evaluation. -/
theorem pow_mod_eq_of_eq {a b m r a' b' m' r' : ℕ} (ha : a = a') (hb : b = b') (hm : m = m')
    (hr : r = r') (h : Nat.mod (Nat.pow a' b') m' = r') : a ^ b % m = r := by
  subst ha hb hm hr
  exact h

end CAS.NumberTheory
