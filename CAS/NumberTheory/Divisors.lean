/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Divisors, divisor sums and the totient from a counting certificate

A list `l` is the list of divisors of `n > 0` when it increases strictly, every entry divides
`n`, its entries `d ≤ m` are as many as the divisors of `n` in `[1, m]` for an `m` with
`n < (m + 1)²`, and `d ↦ n / d` reverses it. The count takes `m` divisions, so with `m = ⌊√n⌋`
the kernel checks the divisors of a number below `10^12` with at most `10^6` divisions. The
divisor sums `σ_k n` follow from the same certificate. The totient is a count of the `d < n`
coprime to `n`, or a product over the prime factors of `n` when they are known.

## Main definitions

* `CAS.NumberTheory.rangeSum`: a sum over an interval of naturals, split in halves a given
  number of times.
* `CAS.NumberTheory.cert`: the divisor certificate, a Boolean.

## Main results

* `CAS.NumberTheory.divisors_eq_of_cert`: `Nat.divisors n = l.toFinset` for a list that passes
  the certificate.
* `CAS.NumberTheory.sigma_eq_of_cert`: `ArithmeticFunction.sigma k n` from the certificate.
* `CAS.NumberTheory.totient_eq_rangeSum`: `Nat.totient n` as a sum of indicators over `[0, n)`.
* `CAS.NumberTheory.totient_eq_of_primeFactorsList`: `Nat.totient n` from the prime factors of
  `n`.
* `CAS.NumberTheory.toFinset_append_eq_insertAll`: a long Finset literal from its list, one
  piece at a time.

## Implementation notes

The certificate rests on the classical pairing of a divisor `d` with `n / d`, one of which is
at most `m` when `n < (m + 1)²`. The count shows that every divisor `d ≤ m` is listed, and the
reversal then gives the cofactors above `m`.

Every check is written with `Nat.rec` and `List.rec` over `Nat.blt`, `Nat.beq`, `Nat.ble`,
`Nat.mod`, `Nat.div` and `Nat.sub`, which the kernel computes on literals with GMP, so
`Eq.refl true` proves `cert n m depth l = true` without unfolding a `Decidable` instance. The
definitions are `noncomputable` because the code generator does not compile recursors; only the
kernel runs them. A recursor chain as long as the interval makes the kernel recurse too deeply,
so `rangeSum` halves the interval `depth` times and leaves at most 512 terms to each leaf, and
the commands compare the Finset literal with the list in pieces of 512 entries.

## References

* The mathlib Community, "The Lean Mathematical Library", in *Proceedings of the 9th ACM SIGPLAN
  International Conference on Certified Programs and Proofs (CPP 2020)*, ACM, 2020, pp. 367-381,
  <https://doi.org/10.1145/3372885.3373824>.
  The statements are about its `Nat.divisors`, `ArithmeticFunction.sigma` and `Nat.totient`;
  the product formula is its `Nat.totient_eq_div_primeFactors_mul`.
-/

@[expose] public section

namespace CAS.NumberTheory

open Finset

/-- `sumLeaf f len lo` is `∑ d ∈ [lo, lo + len), f d`, by a recursor on `len`. -/
noncomputable def sumLeaf (f : ℕ → ℕ) (len : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ ↦ ℕ → ℕ) (fun _ ↦ 0)
    (fun _ ih d ↦ Nat.add (f d) (ih (Nat.succ d))) len

/-- `rangeSum f depth lo len` is `∑ d ∈ [lo, lo + len), f d`, with the interval halved `depth`
times before `sumLeaf` sums the pieces. -/
noncomputable def rangeSum (f : ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, len => sumLeaf f len lo
  | depth + 1, lo, len =>
    rangeSum f depth lo (len / 2) + rangeSum f depth (lo + len / 2) (len - len / 2)

/-- `sumLeaf f len lo` is the sum of `f` over `[lo, lo + len)`. -/
theorem sumLeaf_eq (f : ℕ → ℕ) : ∀ len lo : ℕ, sumLeaf f len lo = ∑ d ∈ Ico lo (lo + len), f d
  | 0, lo => by simp [sumLeaf]
  | len + 1, lo => by
    change f lo + sumLeaf f len (lo + 1) = _
    rw [sumLeaf_eq f len (lo + 1), Finset.sum_eq_sum_Ico_succ_bot (by omega : lo < lo + (len + 1)),
      show lo + 1 + len = lo + (len + 1) by omega]

/-- `rangeSum f depth lo len` is the sum of `f` over `[lo, lo + len)`, for every `depth`. -/
theorem rangeSum_eq (f : ℕ → ℕ) : ∀ depth lo len : ℕ,
    rangeSum f depth lo len = ∑ d ∈ Ico lo (lo + len), f d
  | 0, lo, len => sumLeaf_eq f len lo
  | depth + 1, lo, len => by
    rw [rangeSum, rangeSum_eq f depth, rangeSum_eq f depth,
      show lo + len / 2 + (len - len / 2) = lo + len by omega]
    exact Finset.sum_Ico_consecutive _ (by omega) (by omega)

/-- The number of `d ∈ [lo, lo + len)` with `p d` is the range sum of `1 - g d`, when `g d = 0`
exactly for the `d` with `p d`. -/
theorem card_filter_eq_rangeSum {p : ℕ → Prop} [DecidablePred p] {g : ℕ → ℕ} {lo len : ℕ}
    (hg : ∀ d ∈ Ico lo (lo + len), g d = 0 ↔ p d) (depth : ℕ) :
    ((Ico lo (lo + len)).filter p).card = rangeSum (fun d ↦ Nat.sub 1 (g d)) depth lo len := by
  rw [rangeSum_eq, Finset.card_filter]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  change (if p d then 1 else 0) = 1 - g d
  split_ifs with h
  · have := (hg d hd).mpr h
    omega
  · have : g d ≠ 0 := fun h0 ↦ h ((hg d hd).mp h0)
    omega

/-- `increasingFrom l lo` checks that `lo < d₁ < d₂ < ⋯` for `l = [d₁, d₂, …]`. -/
noncomputable def increasingFrom (l : List ℕ) : ℕ → Bool :=
  List.rec (motive := fun _ ↦ ℕ → Bool) (fun _ ↦ true)
    (fun d _ ih lo ↦ and (Nat.blt lo d) (ih d)) l

/-- A list that passes `increasingFrom l lo` has entries above `lo` and increases strictly. -/
theorem increasingFrom_sound : ∀ {l : List ℕ} {lo : ℕ}, increasingFrom l lo = true →
    (∀ d ∈ l, lo < d) ∧ l.Pairwise (· < ·)
  | [], _, _ => ⟨by simp, List.Pairwise.nil⟩
  | d :: l, lo, h => by
    change and (Nat.blt lo d) (increasingFrom l d) = true at h
    rw [Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨h1, h2⟩ := increasingFrom_sound h.2
    refine ⟨?_, List.Pairwise.cons (fun e he ↦ h1 e he) h2⟩
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact h.1
    · exact h.1.trans (h1 e he)

/-- `allZero f l` checks that `f d = 0` for every entry `d` of `l`. -/
noncomputable def allZero (f : ℕ → ℕ) (l : List ℕ) : Bool :=
  List.rec (motive := fun _ ↦ Bool) true (fun d _ ih ↦ and (Nat.beq (f d) 0) ih) l

/-- `f` vanishes on the entries of a list that passes `allZero f`. -/
theorem allZero_sound {f : ℕ → ℕ} : ∀ {l : List ℕ}, allZero f l = true → ∀ d ∈ l, f d = 0
  | [], _ => by simp
  | d :: l, h => by
    change and (Nat.beq (f d) 0) (allZero f l) = true at h
    rw [Bool.and_eq_true, Nat.beq_eq] at h
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact h.1
    · exact allZero_sound h.2 e he

/-- `sumIs f l s` checks that the values `f d` at the entries `d` of `l` sum to `s`, by
subtracting them from `s` one at a time. -/
noncomputable def sumIs (f : ℕ → ℕ) (l : List ℕ) : ℕ → Bool :=
  List.rec (motive := fun _ ↦ ℕ → Bool) (fun s ↦ Nat.beq s 0)
    (fun d _ ih s ↦ and (Nat.ble (f d) s) (ih (Nat.sub s (f d)))) l

/-- `(l.map f).sum = s` when `sumIs f l s` holds. -/
theorem sumIs_sound {f : ℕ → ℕ} : ∀ {l : List ℕ} {s : ℕ}, sumIs f l s = true →
    (l.map f).sum = s
  | [], s, h => by
    change Nat.beq s 0 = true at h
    rw [Nat.beq_eq] at h
    subst h
    simp
  | d :: l, s, h => by
    change and (Nat.ble (f d) s) (sumIs f l (Nat.sub s (f d))) = true at h
    rw [Bool.and_eq_true, Nat.ble_eq] at h
    obtain ⟨h1, h2⟩ := h
    rw [List.map_cons, List.sum_cons, sumIs_sound h2]
    change f d + (s - f d) = s
    omega

/-- `mapEq f l r` checks that `l.map f = r`. -/
noncomputable def mapEq (f : ℕ → ℕ) (l : List ℕ) : List ℕ → Bool :=
  List.rec (motive := fun _ ↦ List ℕ → Bool)
    (fun r ↦ List.rec (motive := fun _ ↦ Bool) true (fun _ _ _ ↦ false) r)
    (fun d _ ih r ↦ List.rec (motive := fun _ ↦ Bool) false
      (fun e r' _ ↦ and (Nat.beq (f d) e) (ih r')) r) l

/-- `l.map f = r` when `mapEq f l r` holds. -/
theorem mapEq_sound {f : ℕ → ℕ} : ∀ {l r : List ℕ}, mapEq f l r = true → l.map f = r
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | d :: l, e :: r, h => by
    change and (Nat.beq (f d) e) (mapEq f l r) = true at h
    rw [Bool.and_eq_true, Nat.beq_eq] at h
    rw [List.map_cons, h.1, mapEq_sound h.2]

/-- `reverseOnto l r` is `l.reverse ++ r`, by a recursor on `l`. -/
noncomputable def reverseOnto (l : List ℕ) : List ℕ → List ℕ :=
  List.rec (motive := fun _ ↦ List ℕ → List ℕ) (fun r ↦ r) (fun d _ ih r ↦ id (ih (d :: r))) l

/-- `reverseOnto l r = l.reverse ++ r`. -/
theorem reverseOnto_eq : ∀ l r : List ℕ, reverseOnto l r = l.reverse ++ r
  | [], _ => rfl
  | d :: l, r => by
    change reverseOnto l (d :: r) = _
    rw [reverseOnto_eq l, List.reverse_cons, List.append_assoc, List.singleton_append]

/-- The sum of `1 - (d - m)` over the entries `d` of `l` counts the entries `d ≤ m`. -/
theorem sum_map_sub_eq_length_filter (m : ℕ) : ∀ l : List ℕ,
    (l.map fun d ↦ Nat.sub 1 (Nat.sub d m)).sum = (l.filter (· ≤ m)).length
  | [] => rfl
  | d :: l => by
    rw [List.map_cons, List.sum_cons, sum_map_sub_eq_length_filter m l]
    by_cases h : d ≤ m
    · rw [List.filter_cons_of_pos (by simpa using h), List.length_cons]
      change 1 - (d - m) + _ = _
      omega
    · rw [List.filter_cons_of_neg (by simpa using h)]
      change 1 - (d - m) + _ = _
      omega

/-- The divisor certificate of `n`: `0 < n < (m + 1)²`; the list `l` increases strictly from `0`;
every entry divides `n`; the entries `d ≤ m` are as many as the divisors of `n` in `[1, m]`,
counted by `rangeSum` with `depth` halvings; and `d ↦ n / d` reverses `l`. -/
noncomputable def cert (n m depth : ℕ) (l : List ℕ) : Bool :=
  and (Nat.blt 0 n) <| and (Nat.blt n ((m + 1) * (m + 1))) <|
  and (increasingFrom l 0) <| and (allZero (fun d ↦ Nat.mod n d) l) <|
  and (sumIs (fun d ↦ Nat.sub 1 (Nat.sub d m)) l
    (rangeSum (fun d ↦ Nat.sub 1 (Nat.mod n d)) depth 1 m)) <|
  mapEq (fun d ↦ Nat.div n d) l (reverseOnto l [])

/-- A list that passes the divisor certificate of `n` lists the divisors of `n`. -/
theorem divisors_eq_of_cert {n m depth : ℕ} {l : List ℕ} (h : cert n m depth l = true) :
    Nat.divisors n = l.toFinset := by
  simp only [cert, Bool.and_eq_true, Nat.blt_eq] at h
  obtain ⟨hn, hm, hinc, hall, hcount, hrev⟩ := h
  obtain ⟨hpos, hpw⟩ := increasingFrom_sound hinc
  have hl : ∀ d ∈ l, d ∣ n := fun d hd ↦ Nat.dvd_of_mod_eq_zero (allZero_sound hall d hd)
  have hrev' : l.map (n / ·) = l.reverse := by
    have := mapEq_sound hrev
    rwa [reverseOnto_eq, List.append_nil] at this
  have hnd : l.Nodup := hpw.imp Nat.ne_of_lt
  have hsmall : ∀ d, 1 ≤ d → d ≤ m → d ∣ n → d ∈ l := by
    have hsub : (l.filter (· ≤ m)).toFinset ⊆ (Ico 1 (1 + m)).filter (· ∣ n) := by
      intro d hd
      simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hd
      simp only [Finset.mem_filter, Finset.mem_Ico]
      exact ⟨⟨hpos d hd.1, by omega⟩, hl d hd.1⟩
    have hcard : ((Ico 1 (1 + m)).filter (· ∣ n)).card ≤ (l.filter (· ≤ m)).toFinset.card := by
      refine le_of_eq ?_
      rw [List.toFinset_card_of_nodup (hnd.filter _), ← sum_map_sub_eq_length_filter m l,
        sumIs_sound hcount]
      exact card_filter_eq_rangeSum (p := (· ∣ n)) (g := fun d ↦ Nat.mod n d)
        (fun d _ ↦ (Nat.dvd_iff_mod_eq_zero ..).symm) depth
    have hS := Finset.eq_of_subset_of_card_le hsub hcard
    intro d h1 h2 hd
    have : d ∈ (Ico 1 (1 + m)).filter (· ∣ n) := by
      simp only [Finset.mem_filter, Finset.mem_Ico]
      exact ⟨⟨h1, by omega⟩, hd⟩
    rw [← hS, List.mem_toFinset] at this
    exact List.mem_of_mem_filter this
  ext d
  simp only [Nat.mem_divisors, List.mem_toFinset]
  constructor
  · rintro ⟨hd, -⟩
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd hn
    by_cases hdm : d ≤ m
    · exact hsmall d hd0 hdm hd
    · obtain ⟨e, hde⟩ := hd
      have he0 : 0 < e := Nat.pos_of_mul_pos_left (hde ▸ hn)
      have hem : e ≤ m := by
        by_contra hcon
        have : (m + 1) * (m + 1) ≤ d * e := Nat.mul_le_mul (by omega) (by omega)
        omega
      have he : e ∈ l := hsmall e he0 hem (Dvd.intro_left d hde.symm)
      have : n / e ∈ l.map (n / ·) := List.mem_map_of_mem he
      rw [hrev', List.mem_reverse, hde, Nat.mul_div_cancel _ he0] at this
      exact this
  · intro hdl
    exact ⟨hl d hdl, hn.ne'⟩

/-- `σ_k n = s` when `l` passes the divisor certificate of `n` and the `k`-th powers of its
entries sum to `s`. -/
theorem sigma_eq_of_cert {k n m depth s : ℕ} {l : List ℕ} (h : cert n m depth l = true)
    (hs : sumIs (fun d ↦ Nat.pow d k) l s = true) : ArithmeticFunction.sigma k n = s := by
  have hinc : increasingFrom l 0 = true := by
    simp only [cert, Bool.and_eq_true] at h
    exact h.2.2.1
  rw [ArithmeticFunction.sigma_apply, divisors_eq_of_cert h,
    List.sum_toFinset _ ((increasingFrom_sound hinc).2.imp Nat.ne_of_lt)]
  exact sumIs_sound hs

/-- `insertChain a [b, c, …]` is the Finset literal `{a, b, c, …}`, built with `insert`. -/
noncomputable def insertChain (a : ℕ) (l : List ℕ) : Finset ℕ :=
  List.rec (motive := fun _ ↦ ℕ → Finset ℕ) (fun a ↦ {a}) (fun b _ ih a ↦ insert a (ih b)) l a

/-- `(a :: l).toFinset` is the Finset literal of the entries of `a :: l`. -/
theorem toFinset_eq_insertChain : ∀ (a : ℕ) (l : List ℕ), (a :: l).toFinset = insertChain a l
  | a, [] => by simp [insertChain]
  | a, b :: l => by
    rw [List.toFinset_cons, toFinset_eq_insertChain b l]
    rfl

/-- `insertAll [d₁, …, dₖ] s` is `insert d₁ (⋯ (insert dₖ s))`. -/
noncomputable def insertAll (l : List ℕ) (s : Finset ℕ) : Finset ℕ :=
  List.rec (motive := fun _ ↦ Finset ℕ) s (fun d _ ih ↦ insert d ih) l

/-- `(l₁ ++ l₂).toFinset` inserts the entries of `l₁` into `s` when `l₂.toFinset = s`. -/
theorem toFinset_append_eq_insertAll (l₁ : List ℕ) {l₂ : List ℕ} {s : Finset ℕ}
    (h : l₂.toFinset = s) : (l₁ ++ l₂).toFinset = insertAll l₁ s := by
  induction l₁ with
  | nil => exact h
  | cons d l ih =>
    rw [List.cons_append, List.toFinset_cons, ih]
    rfl

/-- `φ n` is the sum over `d ∈ [0, n)` of `1 - (gcd n d - 1)`, the indicator of `gcd n d = 1`,
for every `depth`. -/
theorem totient_eq_rangeSum (n depth : ℕ) :
    Nat.totient n = rangeSum (fun d ↦ Nat.sub 1 (Nat.sub (Nat.gcd n d) 1)) depth 0 n := by
  have := card_filter_eq_rangeSum (p := n.Coprime) (g := fun d ↦ Nat.sub (Nat.gcd n d) 1)
    (lo := 0) (len := n) (fun d hd ↦ by
      have : 0 < Nat.gcd n d := Nat.gcd_pos_of_pos_left _ (by simp at hd; omega)
      change Nat.gcd n d - 1 = 0 ↔ Nat.gcd n d = 1
      omega) depth
  rw [Nat.totient, Finset.range_eq_Ico, ← this, zero_add]

/-- `φ n = n / ∏ p * ∏ (p - 1)`, both products over the list `s` of the distinct prime factors
of `n`, given the list `l` of its prime factors and `s = l.dedup`. -/
theorem totient_eq_of_primeFactorsList {n : ℕ} {l s : List ℕ} (h : Nat.primeFactorsList n = l)
    (hs : l.dedup = s) : Nat.totient n = n / s.prod * (s.map (· - 1)).prod := by
  have hnd : s.Nodup := hs ▸ List.nodup_dedup l
  have hpf : n.primeFactors = s.toFinset := by
    rw [Nat.primeFactors, h]
    ext p
    simp [← hs]
  rw [Nat.totient_eq_div_primeFactors_mul, hpf, List.prod_toFinset _ hnd,
    List.prod_toFinset _ hnd, List.map_id']

end CAS.NumberTheory
