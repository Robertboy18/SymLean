/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Polynomial.RealRoot.Sturm

/-!
# Function variation and finite unit drops

The topological and combinatorial part of Sturm's theorem. The checker's
exact endpoint signs are read as signs of real-valued functions, sign
variation is locally stable, and finitely many unit drops telescope to a
cardinality formula.

The telescoping theorem is independent of polynomials.  It applies to any
natural-valued function that is constant between a finite set of points and
drops by one across each point.

`variationAt_eq_functionVariationAt` identifies the executable variation of a certificate with
the function-level variation `functionVariationAt`.

## Implementation notes

`functionSignsAt` omits zero values before signs are compared, as Sturm does for an intermediate
member that vanishes at an endpoint (no. 8 of the memoir). Sturm's conclusion (no. 6), that the
variations lost from `A` to `B` count the roots of the first function between them, is the
telescoping theorem `eq_add_ncard_of_finite_unit_drops`, proved by induction on the number of
points of the finite set between the endpoints.

## References

* C. Sturm, "Mémoire sur la résolution des équations numériques", *Mémoires présentés par divers
  savans à l'Académie royale des sciences de l'Institut de France, Sciences mathématiques et
  physiques* 6 (1835), pp. 271-318, <https://archive.org/details/mmoirespresent06scie>.
  The count of roots by lost variations (no. 6) and intermediate members that vanish at an
  endpoint (no. 8).
-/

@[expose] public section

namespace CAS.Polynomial.RealRoot

open Filter Set
open scoped Topology
open Sparse

namespace SturmCertificate

/-- The zero-free `SignType.sign` sequence of a list of real-valued functions at `x`. -/
noncomputable def functionSignsAt (functions : List (ℝ → ℝ)) (x : ℝ) :
    List SignType :=
  functions.filterMap fun function ↦
    let sign := SignType.sign (function x)
    if sign = 0 then none else some sign

/-- Sign variation of a list of real-valued functions at `x`. -/
noncomputable def functionVariationAt (functions : List (ℝ → ℝ)) (x : ℝ) : Nat :=
  signVariations (functionSignsAt functions x)

/-- A single function contributes no adjacent sign variations. -/
@[simp]
theorem functionVariationAt_single (function : ℝ → ℝ) (x : ℝ) :
    functionVariationAt [function] x = 0 := by
  by_cases hzero : function x = 0 <;>
    simp [functionVariationAt, functionSignsAt, hzero, signVariations]

/-- A zero head sign is omitted from `functionSignsAt`. -/
theorem functionSignsAt_cons_of_sign_eq_zero
    {function : ℝ → ℝ} {functions : List (ℝ → ℝ)} {x : ℝ}
    (hzero : SignType.sign (function x) = 0) :
    functionSignsAt (function :: functions) x =
      functionSignsAt functions x := by
  simp [functionSignsAt, sign_eq_zero_iff.mp hzero]

/-- A nonzero head sign is kept by `functionSignsAt`. -/
theorem functionSignsAt_cons_of_sign_ne_zero
    {function : ℝ → ℝ} {functions : List (ℝ → ℝ)} {x : ℝ}
    (hnonzero : SignType.sign (function x) ≠ 0) :
    functionSignsAt (function :: functions) x =
      SignType.sign (function x) :: functionSignsAt functions x := by
  simp [functionSignsAt, sign_ne_zero.mp hnonzero]

/--
The checker's exact rational endpoint variation is the variation of the same
chain interpreted as real polynomial functions.
-/
theorem variationAt_eq_functionVariationAt
    (certificate : SturmCertificate) (x : Rat) :
    certificate.variationAt x =
      functionVariationAt
        (certificate.chain.map Sparse.evalReal) (x : ℝ) := by
  have hsign (value : Rat) :
      SignType.sign (value : ℝ) = SignType.sign value :=
    (show StrictMono (Rat.castHom ℝ) from Rat.cast_strictMono).sign_comp value
  simp [variationAt, functionVariationAt, functionSignsAt,
    Sparse.evalReal_ratCast, hsign]

/-- Repeating a nonzero sign at the head creates no new variation. -/
@[simp]
theorem signVariations_cons_self (sign : SignType)
    (rest : List SignType) :
    signVariations (sign :: sign :: rest) =
      signVariations (sign :: rest) := by
  simp [signVariations]

/-- Opposite head signs create exactly one new variation. -/
theorem signVariations_cons_ne {first second : SignType}
    (hne : first ≠ second) (rest : List SignType) :
    signVariations (first :: second :: rest) =
      signVariations (second :: rest) + 1 := by
  simp [signVariations, hne, Nat.add_comm]

/-- Equal nonzero head signs leave function variation unchanged. -/
theorem functionVariationAt_cons_eq
    {first second : ℝ → ℝ} {rest : List (ℝ → ℝ)}
    {x : ℝ} {sign : SignType}
    (hsign : sign ≠ 0)
    (hfirst : SignType.sign (first x) = sign)
    (hsecond : SignType.sign (second x) = sign) :
    functionVariationAt (first :: second :: rest) x =
      functionVariationAt (second :: rest) x := by
  have hfirstNonzero : SignType.sign (first x) ≠ 0 := hfirst ▸ hsign
  have hsecondNonzero : SignType.sign (second x) ≠ 0 := hsecond ▸ hsign
  rw [functionVariationAt, functionVariationAt, functionSignsAt_cons_of_sign_ne_zero hfirstNonzero,
    functionSignsAt_cons_of_sign_ne_zero hsecondNonzero, hfirst, hsecond,
    signVariations_cons_self]

/-- Distinct nonzero head signs add exactly one function variation. -/
theorem functionVariationAt_cons_ne
    {first second : ℝ → ℝ} {rest : List (ℝ → ℝ)}
    {x : ℝ} {firstSign secondSign : SignType}
    (hfirstSign : firstSign ≠ 0)
    (hsecondSign : secondSign ≠ 0)
    (hfirst : SignType.sign (first x) = firstSign)
    (hsecond : SignType.sign (second x) = secondSign)
    (hne : firstSign ≠ secondSign) :
    functionVariationAt (first :: second :: rest) x =
      functionVariationAt (second :: rest) x + 1 := by
  have hfirstNonzero : SignType.sign (first x) ≠ 0 := hfirst ▸ hfirstSign
  have hsecondNonzero : SignType.sign (second x) ≠ 0 := hsecond ▸ hsecondSign
  rw [functionVariationAt, functionVariationAt, functionSignsAt_cons_of_sign_ne_zero hfirstNonzero,
    functionSignsAt_cons_of_sign_ne_zero hsecondNonzero, hfirst, hsecond,
    signVariations_cons_ne hne]

/-- A continuous nonzero function has locally constant sign. -/
theorem eventually_sign_eq_of_continuousAt
    {function : ℝ → ℝ} {x : ℝ}
    (hcontinuous : ContinuousAt function x)
    (hnonzero : function x ≠ 0) :
    ∀ᶠ y in 𝓝 x,
      SignType.sign (function y) = SignType.sign (function x) := by
  rcases lt_or_gt_of_ne hnonzero with hnegative | hpositive
  · filter_upwards [hcontinuous.eventually_lt continuousAt_const hnegative] with y hy
    rw [sign_neg hy, sign_neg hnegative]
  · filter_upwards [continuousAt_const.eventually_lt hcontinuous hpositive] with y hy
    rw [sign_pos hy, sign_pos hpositive]

/--
If the first two nonzero signs and the suffix variation are unchanged, adding
the first function preserves the full variation.
-/
theorem functionVariationAt_cons_stable
    {first second : ℝ → ℝ} {tail : List (ℝ → ℝ)}
    {x y : ℝ}
    (hfirstNonzero : first x ≠ 0)
    (hsecondNonzero : second x ≠ 0)
    (hfirst :
      SignType.sign (first y) = SignType.sign (first x))
    (hsecond :
      SignType.sign (second y) = SignType.sign (second x))
    (hsuffix :
      functionVariationAt (second :: tail) y =
        functionVariationAt (second :: tail) x) :
    functionVariationAt (first :: second :: tail) y =
      functionVariationAt (first :: second :: tail) x := by
  have hfirstSign : SignType.sign (first x) ≠ 0 := sign_ne_zero.mpr hfirstNonzero
  have hsecondSign : SignType.sign (second x) ≠ 0 := sign_ne_zero.mpr hsecondNonzero
  by_cases hsigns : SignType.sign (first x) = SignType.sign (second x)
  · rw [functionVariationAt_cons_eq hfirstSign hfirst (hsecond.trans hsigns.symm),
      functionVariationAt_cons_eq hfirstSign rfl hsigns.symm, hsuffix]
  · rw [functionVariationAt_cons_ne hfirstSign hsecondSign hfirst hsecond hsigns,
      functionVariationAt_cons_ne hfirstSign hsecondSign rfl rfl hsigns, hsuffix]

/--
If the first and third nonzero signs are opposite, an arbitrary middle value
contributes exactly one variation after omitted zeros are accounted for.
-/
theorem functionVariationAt_skip_middle_of_opposite
    {first middle third : ℝ → ℝ} {tail : List (ℝ → ℝ)}
    {x : ℝ} {firstSign thirdSign : SignType}
    (hfirstSign : firstSign ≠ 0)
    (hthirdSign : thirdSign ≠ 0)
    (hfirst : SignType.sign (first x) = firstSign)
    (hthird : SignType.sign (third x) = thirdSign)
    (hopposite : firstSign ≠ thirdSign) :
    functionVariationAt (first :: middle :: third :: tail) x =
      functionVariationAt (third :: tail) x + 1 := by
  have hfirstNonzero : SignType.sign (first x) ≠ 0 := hfirst ▸ hfirstSign
  have hthirdNonzero : SignType.sign (third x) ≠ 0 := hthird ▸ hthirdSign
  unfold functionVariationAt
  rw [functionSignsAt_cons_of_sign_ne_zero hfirstNonzero]
  by_cases hmiddleZero : SignType.sign (middle x) = 0
  · rw [functionSignsAt_cons_of_sign_eq_zero hmiddleZero,
      functionSignsAt_cons_of_sign_ne_zero hthirdNonzero, hfirst, hthird]
    exact signVariations_cons_ne hopposite _
  · rw [functionSignsAt_cons_of_sign_ne_zero hmiddleZero,
      functionSignsAt_cons_of_sign_ne_zero hthirdNonzero, hfirst, hthird]
    cases firstSign <;>
      cases hmiddle : SignType.sign (middle x) <;>
      cases thirdSign <;>
      simp_all [signVariations, Nat.add_comm]

/--
Finite unit jumps telescope on the real line.

This is the global topological-combinatorial core of Sturm's theorem,
independent of polynomials.  A natural-valued function which is constant on
every root-free interval and drops by one across every point of a finite set
satisfies the expected endpoint-count identity.
-/
theorem eq_add_ncard_of_finite_unit_drops
    (variation : ℝ → Nat) (roots : Set ℝ)
    (hfinite : roots.Finite)
    (hconstant :
      ∀ {a b : ℝ}, a ≤ b → a ∉ roots → b ∉ roots →
        (∀ x ∈ Ioo a b, x ∉ roots) →
          variation a = variation b)
    (hdrop :
      ∀ root ∈ roots, ∃ base : Nat,
        (∀ᶠ x in 𝓝[<] root, variation x = base + 1) ∧
        (∀ᶠ x in 𝓝[>] root, variation x = base)) :
    ∀ {a b : ℝ}, a ≤ b → a ∉ roots → b ∉ roots →
      variation a =
        variation b + (roots ∩ Ioo a b).ncard := by
  classical
  intro a b hab ha hb
  obtain ⟨count, hcount⟩ : ∃ n, (roots ∩ Ioo a b).ncard = n := ⟨_, rfl⟩
  induction count generalizing a b with
  | zero =>
      have hempty := (Set.ncard_eq_zero (hfinite.inter_of_left _)).mp hcount
      rw [hcount, add_zero]
      exact hconstant hab ha hb fun x hx hxr ↦ hempty.subset ⟨hxr, hx⟩
  | succ n ih =>
      set intervalRoots := roots ∩ Ioo a b
      have hintervalFinite : intervalRoots.Finite := hfinite.inter_of_left _
      obtain ⟨root, hrootInterval, hrootLeast⟩ := Set.exists_min_image intervalRoots id
        hintervalFinite (Set.nonempty_of_ncard_ne_zero (by omega))
      obtain ⟨hroot, haroot, hrootb⟩ := hrootInterval
      obtain ⟨base, hleftDrop, hrightDrop⟩ := hdrop root hroot
      -- Below the least root the interval `(a, root)` is root-free.
      have hfree : ∀ x, a < x → x < root → x ∉ roots := fun x hax hxroot hx ↦
        absurd (hrootLeast x ⟨hx, hax, hxroot.trans hrootb⟩) (not_le.mpr hxroot)
      obtain ⟨left, hleftValue, haleft, hleftroot⟩ :=
        (hleftDrop.and (Ioo_mem_nhdsLT haroot)).exists
      have havariation : variation a = base + 1 :=
        (hconstant haleft.le ha (hfree left haleft hleftroot)
          fun x hx ↦ hfree x hx.1 (hx.2.trans hleftroot)).trans hleftValue
      -- Just above `root`, before every remaining root, the variation is `base`.
      set remaining := intervalRoots \ {root}
      have hremainingGt : ∀ y ∈ remaining, root < y := fun y hy ↦
        lt_of_le_of_ne (hrootLeast y hy.1) (Ne.symm hy.2)
      obtain ⟨right, hrightValue, ⟨hrootRight, hrightb⟩, hrightLeast⟩ :=
        (hrightDrop.and (Filter.Eventually.and (Ioo_mem_nhdsGT hrootb)
          ((Filter.eventually_all_finite hintervalFinite.sdiff).2
            fun y hy ↦ Ioo_mem_nhdsGT (hremainingGt y hy)))).exists
      have hremainingInterval : roots ∩ Ioo right b = remaining := by
        ext x
        constructor
        · rintro ⟨hx, hrightx, hxb⟩
          exact ⟨⟨hx, haroot.trans (hrootRight.trans hrightx), hxb⟩, (hrootRight.trans hrightx).ne'⟩
        · exact fun hx ↦ ⟨hx.1.1, (hrightLeast x hx).2, hx.1.2.2⟩
      have hrightNotRoot : right ∉ roots := fun hrightRoot ↦ lt_irrefl right
        (hrightLeast right ⟨⟨hrightRoot, haroot.trans hrootRight, hrightb⟩, hrootRight.ne'⟩).2
      have hcard : remaining.ncard + 1 = intervalRoots.ncard :=
        Set.ncard_sdiff_singleton_add_one ⟨hroot, haroot, hrootb⟩ hintervalFinite
      rw [← hremainingInterval] at hcard
      have hrightToEnd := ih hrightb.le hrightNotRoot hb (by omega)
      omega

end SturmCertificate

end CAS.Polynomial.RealRoot
