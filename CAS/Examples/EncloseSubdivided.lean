/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS

/-!
# A subdivided enclosure: `#cas (depth := n) [enclose]`

`#cas (depth := 3) [enclose x in [0, 2]] (sin x * cos x)` bisects `[0, 2]` to depth `3` before it
encloses the range, inside `#guard_msgs`, which checks its report. It takes about a minute, so it
has a module of its own.
-/

/-! ## Executed checks -/

set_option linter.hashCommand false
set_option linter.privateModule false

set_option linter.style.longLine false in
/--
info: #cas (depth := 3) [enclose x in [0, 2]]
Domain: x ∈ [0, 2] ⊆ ℝ
Input (scalar map ℝ → ℝ): (sin x * cos x)
Output (certified interval in ℝ): [-0.378402, 0.544012]
Upper bound: 0.544012
Absolute bound: 0.544012
Center and radius: ≈0.082805 ± 0.461207

[CAS.Command.details] More details
  Coordinates: x
  Certified domain: x ∈ [0, 2] ⊆ ℝ
  [CAS.Command.computation] Certified numerical guarantee
    Guarantee: the input lies in the output interval throughout the box
    Decimal preview: outward-rounded to 6 places where it is a bound
    Exact certified output: [-2738491939741224980065545710511944340592687821623911616333681165377358429451/7237005577332262213973186563042994240829374041602535252466099000494570602496, 31496104119253840352539446916394688164217738877448090787965650547754896521097/57896044618658097711785492504343953926634992332820282019728792003956564819968]
    Precision policy: exp order 8, sqrt digits 12, log terms 10, subdivision depth 3
  [CAS.explanation] Proof evidence
    [CAS.explanation.checkedEvidence] Checked proof steps
      [CAS.explanation.checkedStep] Enclosure of the input
        Proposition: ∀ x ∈ Set.Icc 0 2, -0.378402 ≤ Real.sin x * Real.cos x ∧ Real.sin x * Real.cos x ≤ 0.544012
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Tactic.BoxInequality.mem_of_enclosedOn_box
      [CAS.explanation.checkedStep] Upper bound of the input
        Proposition: ∀ x ∈ Set.Icc 0 2, Real.sin x * Real.cos x ≤ 0.544012
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Tactic.BoxInequality.le_of_boundOn_box
      [CAS.explanation.checkedStep] Absolute bound of the input
        Proposition: ∀ x ∈ Set.Icc 0 2, |Real.sin x * Real.cos x| ≤ 0.544012
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Tactic.BoxInequality.abs_le_of_boundOn_abs_box
      [CAS.explanation.checkedStep] Center and radius of the input
        Proposition: ∀ x ∈ Set.Icc 0 2, |Real.sin x * Real.cos x - 82805e-6| ≤ 0.461207
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Tactic.BoxInequality.abs_sub_le_of_approxOn_box
      [CAS.explanation.checkedStep] Certified enclosure
        Proposition: CAS.Certificate.EnclosedOn (CAS.Exact.exprFn (𝕏[0].sin.mul 𝕏[0].cos))
          (CAS.Continuum.RationalInterval.boxDomain fun coordinate ↦
            [CAS.Continuum.RationalInterval.ofBounds 0 2 ⋯].get coordinate)
          (↑(-2738491939741224980065545710511944340592687821623911616333681165377358429451) /
            ↑7237005577332262213973186563042994240829374041602535252466099000494570602496)
          (↑31496104119253840352539446916394688164217738877448090787965650547754896521097 /
            ↑57896044618658097711785492504343953926634992332820282019728792003956564819968)
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Continuum.RationalInterval.EnclosureAttempt.enclosedOn_of_interval_eq
      [CAS.explanation.checkedStep] Certified upper bound
        Proposition: CAS.Certificate.BoundOn (CAS.Exact.exprFn (𝕏[0].sin.mul 𝕏[0].cos))
          (CAS.Continuum.RationalInterval.boxDomain fun coordinate ↦
            [CAS.Continuum.RationalInterval.ofBounds 0 2 ⋯].get coordinate)
          (↑31496104119253840352539446916394688164217738877448090787965650547754896521097 /
            ↑57896044618658097711785492504343953926634992332820282019728792003956564819968)
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Continuum.RationalInterval.EnclosureAttempt.boundOn_of_interval_eq
      [CAS.explanation.checkedStep] Certified absolute bound
        Proposition: CAS.Certificate.BoundOn (fun x ↦ |CAS.Exact.exprFn (𝕏[0].sin.mul 𝕏[0].cos) x|)
          (CAS.Continuum.RationalInterval.boxDomain fun coordinate ↦
            [CAS.Continuum.RationalInterval.ofBounds 0 2 ⋯].get coordinate)
          (↑31496104119253840352539446916394688164217738877448090787965650547754896521097 /
            ↑57896044618658097711785492504343953926634992332820282019728792003956564819968)
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Continuum.RationalInterval.EnclosureAttempt.boundOn_abs_of_interval_eq
      [CAS.explanation.checkedStep] Certified center and radius
        Proposition: CAS.Certificate.ApproxOn (CAS.Exact.exprFn (𝕏[0].sin.mul 𝕏[0].cos))
          (fun x ↦
            ↑9588168601324040512015081232299133439476236304456797857296201224736029085489 /
              ↑115792089237316195423570985008687907853269984665640564039457584007913129639936)
          (CAS.Continuum.RationalInterval.boxDomain fun coordinate ↦
            [CAS.Continuum.RationalInterval.ofBounds 0 2 ⋯].get coordinate)
          (↑53404039637183640193063812600490242888959241450439383718635099870773763956705 /
            ↑115792089237316195423570985008687907853269984665640564039457584007913129639936)
        Validation: proof term checked by the kernel against this proposition
        Theorem: CAS.Continuum.RationalInterval.EnclosureAttempt.approxOn_center_of_interval_eq
    [CAS.explanation.plannerMetadata] Planner metadata (not proof)
      [CAS.explanation.plannerStep] checked box subdivision: succeeded
        used by 3 local enclosure routes
      [CAS.explanation.plannerStep] increasing endpoint range: succeeded
        used by 2 local enclosure routes
      [CAS.explanation.plannerStep] centered mean-value form: succeeded
      [CAS.explanation.plannerStep] decreasing endpoint range: succeeded
-/
#guard_msgs in
#cas (depth := 3) [enclose x in [0, 2]] (sin x * cos x)

