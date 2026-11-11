/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Algebra.Polynomial.Inductions
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Balanced coefficient tables

A `CoefficientTree depth` holds `2 ^ depth` natural numbers in a balanced binary tree.
`CoefficientTree.ofFnBlock` builds one from any coefficient function and evaluates only the
requested block, and `CoefficientTree.check` tests a Boolean predicate on every leaf together
with its index. `Polynomial.ofFn_map_coefficients` and `Polynomial.ofFn_mul_scalar` map and scale
the coefficients of `Polynomial.ofFn`.

## Main definitions

* `CoefficientTree.lookup`: the coefficient at an index, found by descending the tree.
* `CoefficientTree.ofFnBlock a depth offset`: the tree of the values of `a` at `offset + i` for
  `i < 2 ^ depth`; `CoefficientTree.ofArrayBlock` reads them from an array padded with zeros.
* `CoefficientTree.check p`: the conjunction of `p (offset + i) (lookup i)` over the leaves.
* `CoefficientTree.pack b`: the sum of `lookup i * b ^ i`, computed on the tree.

## Main results

* `CoefficientTree.lookup_ofFnBlock`: in-range lookups of `ofFnBlock a` return the values of `a`.
* `CoefficientTree.check_sound`, `CoefficientTree.check_of_forall`: `check p offset` is `true`
  exactly when `p (offset + i) (lookup i)` holds for every `i < 2 ^ depth`.

## Implementation notes

A lookup descends `depth` branches, so reading one coefficient of a tree built by `ofFnBlock`
reduces one path and needs the coefficient function at one index only. We keep the storage
behind that function, so the leaves may be slots of packed natural numbers or values computed
on demand.
`check_of_forall` builds the result of `check` from facts proved index by index, for instance in
separate batches, so a large table needs neither a tree written by hand nor one long conjunction.
-/

@[expose] public section

open Polynomial
open scoped BigOperators

namespace Polynomial

/-- Mapping a finite coefficient polynomial maps each of its coefficients. -/
theorem ofFn_map_coefficients {R S : Type*} [Semiring R] [Semiring S]
    [DecidableEq R] [DecidableEq S] (f : R →+* S) {n : ℕ} (v : Fin n → R) :
    (Polynomial.ofFn n v).map f = Polynomial.ofFn n (fun i ↦ f (v i)) := by
  ext i
  by_cases hi : i < n
  · simp [ofFn_coeff_eq_val_of_lt _ hi]
  · simp [ofFn_coeff_eq_zero_of_ge _ (not_lt.1 hi)]

/-- Scaling every coefficient scales its whole polynomial. -/
theorem ofFn_mul_scalar {R : Type*} [Semiring R] [DecidableEq R]
    {n : ℕ} (v : Fin n → R) (c : R) :
    Polynomial.ofFn n (fun i ↦ c * v i) = C c * Polynomial.ofFn n v := by
  change Polynomial.ofFn n (c • v) = _
  rw [map_smul, C_mul']

end Polynomial

namespace CAS.Numerics

/-- A balanced coefficient array, with its power-of-two length carried by the type. -/
inductive CoefficientTree : ℕ → Type
  | leaf (value : ℕ) : CoefficientTree 0
  | branch {depth : ℕ} (left right : CoefficientTree depth) : CoefficientTree (depth + 1)

namespace CoefficientTree

/-- Read a coefficient by descending the balanced table. Only in-range indices are used. -/
def lookup {depth : ℕ} : CoefficientTree depth → ℕ → ℕ
  | .leaf value, _ => value
  | @branch depth left right, i =>
    if i < 2 ^ depth then left.lookup i else right.lookup (i - 2 ^ depth)

/-- Check an indexed predicate on every stored coefficient, starting at an offset. -/
def check (p : ℕ → ℕ → Bool) {depth : ℕ} : CoefficientTree depth → ℕ → Bool
  | .leaf value, offset => p offset value
  | @branch depth left right, offset =>
    left.check p offset && right.check p (offset + 2 ^ depth)

/-- A successful balanced replay verifies the predicate at every in-range lookup. -/
theorem check_sound (p : ℕ → ℕ → Bool) {depth : ℕ}
    (a : CoefficientTree depth) (offset : ℕ) (h : a.check p offset = true)
    {i : ℕ} (hi : i < 2 ^ depth) : p (offset + i) (a.lookup i) = true := by
  induction a generalizing offset i with
  | leaf value => simpa [lookup, check, show i = 0 by simpa using hi] using h
  | @branch depth left right ihl ihr =>
    simp only [check, Bool.and_eq_true] at h
    by_cases hil : i < 2 ^ depth
    · simpa only [lookup, hil, ↓reduceIte] using ihl offset h.1 hil
    · have hir : i - 2 ^ depth < 2 ^ depth := by
        rw [pow_succ, Nat.mul_two] at hi
        omega
      have hoff : offset + 2 ^ depth + (i - 2 ^ depth) = offset + i := by omega
      simpa only [lookup, hil, ↓reduceIte, hoff] using ihr (offset + 2 ^ depth) h.2 hir

/-- Pointwise checks on the represented coefficients verify the balanced replay. -/
theorem check_of_forall (p : ℕ → ℕ → Bool) {depth : ℕ}
    (a : CoefficientTree depth) (offset : ℕ)
    (h : ∀ i : Fin (2 ^ depth), p (offset + i.val) (a.lookup i.val) = true) :
    a.check p offset = true := by
  induction a generalizing offset with
  | leaf value =>
    simpa only [check, lookup, Nat.add_zero] using h ⟨0, by simp⟩
  | @branch depth left right ihl ihr =>
    simp only [check, Bool.and_eq_true]
    constructor
    · refine ihl _ fun i ↦ ?_
      have hi := i.isLt
      simpa only [lookup, hi, ↓reduceIte] using h ⟨i.val, by rw [pow_succ, Nat.mul_two]; omega⟩
    · refine ihr _ fun i ↦ ?_
      have hi := i.isLt
      have hright : ¬2 ^ depth + i.val < 2 ^ depth := by omega
      simpa only [lookup, hright, ↓reduceIte, Nat.add_sub_cancel_left, Nat.add_assoc]
        using h ⟨2 ^ depth + i.val, by rw [pow_succ, Nat.mul_two]; omega⟩

/-- Read a balanced block from any coefficient function. Only the requested
indices are evaluated, so a caller can encode values or provide its own storage. -/
def ofFnBlock (a : ℕ → ℕ) : (depth offset : ℕ) → CoefficientTree depth
  | 0, offset => .leaf (a offset)
  | depth + 1, offset =>
    .branch (ofFnBlock a depth offset) (ofFnBlock a depth (offset + 2 ^ depth))

/-- Each in-range lookup agrees with the supplied coefficient function. -/
theorem lookup_ofFnBlock (a : ℕ → ℕ) (depth offset : ℕ) {i : ℕ}
    (hi : i < 2 ^ depth) :
    (ofFnBlock a depth offset).lookup i = a (offset + i) := by
  induction depth generalizing offset i with
  | zero => simp [ofFnBlock, lookup, show i = 0 by simpa using hi]
  | succ depth ih =>
    by_cases hleft : i < 2 ^ depth
    · simp only [ofFnBlock, lookup, hleft, ↓reduceIte, ih offset hleft]
    · have hright : i - 2 ^ depth < 2 ^ depth := by
        rw [pow_succ, Nat.mul_two] at hi
        omega
      have he : offset + 2 ^ depth + (i - 2 ^ depth) = offset + i := by omega
      simp only [ofFnBlock, lookup, hleft, ↓reduceIte, ih _ hright, he]

/-- Read a balanced block from an array, filling entries beyond its length with zero. -/
def ofArrayBlock (a : Array ℕ) (depth offset : ℕ) : CoefficientTree depth :=
  ofFnBlock (fun i ↦ a[i]?.getD 0) depth offset

/-- Evaluate the packed digits directly on the tree, without repeated table lookups. -/
def pack (b : ℕ) {depth : ℕ} : CoefficientTree depth → ℕ
  | .leaf value => value
  | @branch depth left right => left.pack b + b ^ (2 ^ depth) * right.pack b

end CoefficientTree

end CAS.Numerics
