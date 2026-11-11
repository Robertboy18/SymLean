/-
Copyright (c) 2026 SymLean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SymLean Team
-/

module

public import CAS.Continuum.Quadrature.RationalRule
public import CAS.Continuum.Quadrature.UniformComposite

/-!
# Exact-rational uniform composition of quadrature rules

Any normalized exact-rational rule gives the corresponding normalized rule on
`N` equal panels. A source term `(w, ξ)` on panel `k`
becomes

`(w / N, (k + ξ) / N)`.

The construction is executable, keeps the panel-major accumulation order, and after casting
to real numbers is exactly the analytic `uniformCompositeTerms`
(`uniformComposite_toQuadratureRule_termsOn`). Its value is therefore the exact-real composite
value (`uniformComposite_toQuadratureRule_valueOn`).

## Implementation notes

We compose on the reference interval, before any transport, so the result is again a
`RationalQuadratureRule` that `RationalQuadratureRule.termsOn?` can sample on any `[a, b]`.
`uniformComposite` maps every source term over `List.range N` with one rational division for
the weight and one for the node, so the composite rule has `N` times as many terms. The real
`uniformCompositeTerms` of `CAS.Continuum.Quadrature.UniformComposite` goes the other way: it
transports the real rule to each panel of the mesh. We identify the two lists
term by term, the weights through `uniformMeshPoint_succ_sub` and `field_simp`, the nodes by
unfolding `uniformMeshPoint`, and the value theorem follows from
`weightedSum_uniformCompositeTerms`. No module of SymLean imports these definitions.
-/

@[expose] public section

open Set

namespace CAS.Continuum
namespace RationalQuadratureRule

/--
Compose a normalized exact-rational rule over `N` equal panels of `[0,1]`.

The positivity hypothesis is used only to prove that every transported node remains in the
normalized unit interval.
-/
def uniformComposite
    (rule : RationalQuadratureRule) (N : ℕ) (hN : 0 < N) :
    RationalQuadratureRule where
  terms :=
    (List.range N).flatMap fun k : ℕ ↦
      rule.terms.map fun term ↦
        (term.1 / (N : ℚ), ((k : ℚ) + term.2) / (N : ℚ))
  nodes_mem_unit := by
    intro term hterm
    rw [List.mem_flatMap] at hterm
    obtain ⟨k, hkRange, hterm⟩ := hterm
    have hk : k < N := List.mem_range.mp hkRange
    rw [List.mem_map] at hterm
    obtain ⟨source, hsource, rfl⟩ := hterm
    have hnode := rule.nodes_mem_unit source hsource
    have hNq : (0 : ℚ) < N := by exact_mod_cast hN
    have hkN : (k : ℚ) + 1 ≤ N := by
      exact_mod_cast Nat.succ_le_of_lt hk
    constructor
    · exact div_nonneg
        (add_nonneg (by positivity) hnode.1)
        hNq.le
    · apply (div_le_one hNq).2
      linarith only [hnode.2, hkN]

/--
The exact-rational composite rule produces precisely the ordered
real term list for uniform panel composition.

This is stronger than equality of quadrature values: both lists add the terms
in the same panel-major order.
-/
theorem uniformComposite_toQuadratureRule_termsOn
    (rule : RationalQuadratureRule) (N : ℕ) (hN : 0 < N)
    (f : ℝ → ℝ) (a b : ℝ) :
    (rule.uniformComposite N hN).toQuadratureRule.termsOn f a b =
      uniformCompositeTerms rule.toQuadratureRule f N a b := by
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold uniformComposite toQuadratureRule QuadratureRule.termsOn uniformCompositeTerms
  simp only [List.map_flatMap, List.map_map]
  refine List.flatMap_congr fun k _ ↦ ?_
  simp only [QuadratureRule.termsOn, List.map_map]
  refine List.map_congr_left fun term _ ↦ ?_
  simp only [Function.comp_apply, rationalPairToReal]
  apply Prod.ext
  · push_cast
    rw [uniformMeshPoint_succ_sub a b hN]
    field_simp
  · congr 1
    unfold uniformMeshPoint
    push_cast
    field_simp
    ring_nf

/--
Exact-rational uniform composition denotes the canonical exact-real uniform
composite value on every real interval.
-/
theorem uniformComposite_toQuadratureRule_valueOn
    (rule : RationalQuadratureRule) (N : ℕ) (hN : 0 < N)
    (f : ℝ → ℝ) (a b : ℝ) :
    (rule.uniformComposite N hN).toQuadratureRule.valueOn
        f a b =
      uniformCompositeValue rule.toQuadratureRule f N a b := by
  rw [QuadratureRule.valueOn, uniformComposite_toQuadratureRule_termsOn,
    weightedSum_uniformCompositeTerms]

end RationalQuadratureRule
end CAS.Continuum
