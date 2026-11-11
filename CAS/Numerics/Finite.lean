/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Data.Fin.Basic

/-!
# Finite certificates assembled from batches

`BatchAll p start size` states a predicate on the consecutive indices from `start`, the batch
truncated at the end of the finite domain, and `forall_of_batchAll` assembles batches of positive
size into a proof on every index. `RangeAll` and its lemmas join checked ranges. The predicates
and their proofs are unrestricted, so the same coverage theorems apply to exact arithmetic and to
interval certificates.

## Main definitions

* `RangeAll p start count`: each of the `count` indices from `start` lies in the domain and
  satisfies `p`.
* `batchCount n size`: the number of batches, `0` for an empty domain and the ceiling of
  `n / size` for positive `size`.
* `batchIndex start size j`: the index `start + j` of the domain, for `j` below the truncated
  batch length `min size (n - start)`.
* `BatchAll p start size`: `p` holds on every index of the batch from `start`.

## Main results

* `of_rangeAll`: a checked range gives `p` at every index it covers.
* `rangeAll_singleton`, `rangeAll_zero`, `rangeAll_append`: one checked index, the empty range,
  and the union of two adjacent ranges.
* `forall_of_rangeAll`: a range from `0` covering the domain proves `∀ i, p i`.
* `forall_of_decide_eq_true`: a Boolean decision of `p` that is `true` everywhere proves
  `∀ i, p i`.
* `forall_of_batchAll`: batches of positive size, the last one truncated, prove `∀ i, p i`.
* `claim_of_batch_checks`: a soundness theorem applied to the assembled checks of a witness.

## Implementation notes

We keep three things apart in the certificates of `CAS.Numerics`. Candidate data, proposed by an
external solver and embedded by the importers (`json_data%`, `packed_int_rows%`,
`binary64_words%`), establishes nothing. Finite checks of that data are proved by `cega`
batches. An analytic soundness theorem states what the checks imply, and
`claim_of_batch_checks` applies it to the assembled checks. Checks at finitely many points prove
nothing between them: the soundness theorem supplies that argument, for instance cell coverage
(`coverWalk_sound`), an interpolation or derivative remainder, diagonal dominance turning the
residual rows of a linear solve into an error bound, a quadrature error theorem summed over
panels, or a stability estimate for a trajectory. It belongs beside the checker it justifies.
`RangeAll` checks every index against the domain, so an overlong certificate cannot silently
truncate, and a balanced tree of `rangeAll_append` keeps large proofs shallow.
-/

@[expose] public section

namespace CAS.Numerics

/-- A predicate holds on a consecutive range of a finite domain. Every index is
checked to lie in the domain, so an overlong certificate cannot silently truncate. -/
def RangeAll {n : ℕ} (p : Fin n → Prop) (start count : ℕ) : Prop :=
  ∀ j : Fin count, ∃ h : start + j.val < n, p ⟨start + j.val, h⟩

/-- `Decidable (RangeAll p start count)` for a decidable `p`, by unfolding `RangeAll` to a bounded
quantifier over `Fin count` and inferring the instance. -/
instance {n : ℕ} (p : Fin n → Prop) [DecidablePred p] (start count : ℕ) :
    Decidable (RangeAll p start count) := by
  unfold RangeAll
  infer_instance

/-- A certified consecutive range supplies the predicate at any covered index. -/
theorem of_rangeAll {n start count : ℕ} {p : Fin n → Prop}
    (h : RangeAll p start count) (i : Fin n)
    (hlo : start ≤ i.val) (hhi : i.val < start + count) : p i := by
  obtain ⟨hi, hp⟩ := h ⟨i.val - start, by omega⟩
  simpa only [Nat.add_sub_cancel' hlo] using hp

/-- A checked index is a certified range of length one. -/
theorem rangeAll_singleton {n start : ℕ} {p : Fin n → Prop}
    (hstart : start < n) (h : p ⟨start, hstart⟩) : RangeAll p start 1 := by
  rintro ⟨j, hj⟩
  obtain rfl : j = 0 := by omega
  exact ⟨by simpa using hstart, by simpa using h⟩

/-- An empty range requires no numerical evidence. -/
theorem rangeAll_zero {n start : ℕ} {p : Fin n → Prop} : RangeAll p start 0 :=
  fun j ↦ Fin.elim0 j

/-- Adjacent certified ranges form a certified union. Balanced use of this
lemma keeps large finite proofs shallow, independently of the predicate. -/
theorem rangeAll_append {n start left right : ℕ} {p : Fin n → Prop}
    (hleft : RangeAll p start left) (hright : RangeAll p (start + left) right) :
    RangeAll p start (left + right) := by
  intro j
  by_cases hj : j.val < left
  · exact hleft ⟨j.val, hj⟩
  · obtain ⟨hi, hp⟩ := hright ⟨j.val - left, by have := j.isLt; omega⟩
    change start + left + (j.val - left) < n at hi
    have he : start + left + (j.val - left) = start + j.val := by omega
    exact ⟨by omega, by simpa only [he] using hp⟩

/-- A certified range covering the whole domain proves the finite universal claim. -/
theorem forall_of_rangeAll {n : ℕ} {p : Fin n → Prop}
    (h : RangeAll p 0 n) : ∀ i : Fin n, p i :=
  fun i ↦ of_rangeAll h i (Nat.zero_le _) (by simp)

/-- A Boolean decision of each finite predicate proves the predicate itself.
The decision procedure can be compiled once before indices are specialized. -/
theorem forall_of_decide_eq_true {α : Type*} (p : α → Prop) [DecidablePred p]
    (h : ∀ i, decide (p i) = true) : ∀ i, p i :=
  fun i ↦ of_decide_eq_true (h i)

/-- Number of nonempty batches of a given size; an empty domain needs no batches.
For a positive size this is the ceiling of `n / size`. -/
def batchCount (n size : ℕ) : ℕ :=
  if n = 0 then 0 else (n - 1) / size + 1

/-- The indices in a batch, with its length truncated at the end of the domain. -/
def batchIndex {n : ℕ} (start size : ℕ) (j : Fin (min size (n - start))) : Fin n :=
  ⟨start + j.val, by
    have hj := j.isLt
    have hlen := Nat.min_le_right size (n - start)
    omega⟩

/-- A predicate holds throughout a batch beginning at `start`. -/
def BatchAll {n : ℕ} (p : Fin n → Prop) (start size : ℕ) : Prop :=
  ∀ j : Fin (min size (n - start)), p (batchIndex start size j)

/-- `Decidable (BatchAll p start size)` for a decidable `p`, by unfolding `BatchAll` to a bounded
quantifier over the batch and inferring the instance. -/
instance {n : ℕ} (p : Fin n → Prop) [DecidablePred p] (start size : ℕ) :
    Decidable (BatchAll p start size) := by
  unfold BatchAll
  infer_instance

/-- Consecutive batches of positive size cover every index, including the truncated
final batch. No batch checks are required when the domain is empty. -/
theorem forall_of_batchAll {n size : ℕ} {p : Fin n → Prop} (hsize : 0 < size)
    (hbatch : ∀ b : Fin (batchCount n size), BatchAll p (b.val * size) size) :
    ∀ i : Fin n, p i := by
  intro i
  have hi := i.isLt
  have hquot : i.val / size < batchCount n size := by
    rw [batchCount, ite_eq_right (show ¬n = 0 by omega)]
    have := Nat.div_le_div_right (c := size) (show i.val ≤ n - 1 by omega)
    omega
  have hmod := Nat.mod_lt i.val hsize
  have hdecomp := Nat.div_add_mod' i.val size
  have hoffset : i.val % size < min size (n - i.val / size * size) := by omega
  have heq : batchIndex (i.val / size * size) size ⟨i.val % size, hoffset⟩ = i :=
    Fin.ext hdecomp
  exact heq ▸ hbatch ⟨i.val / size, hquot⟩ ⟨i.val % size, hoffset⟩

/-- A sound numerical checker supplies the hypotheses of an analytic theorem.
The witness can contain coefficients, rational bounds, or interval subdivisions;
`sound` is the mathematical bridge from all checked indices to the final claim. -/
theorem claim_of_batch_checks {W : Type*} {n size : ℕ}
    (check : W → Fin n → Bool) (claim : W → Prop)
    (sound : ∀ w, (∀ i, check w i = true) → claim w) (w : W)
    (hsize : 0 < size)
    (hbatch : ∀ b : Fin (batchCount n size),
      BatchAll (fun i ↦ check w i = true) (b.val * size) size) : claim w :=
  sound w (forall_of_batchAll hsize hbatch)

end CAS.Numerics
