/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Density detected by compact smooth tests in a chart

An internal density criterion for a linear family in `L²`. A measurable
embedding into a Euclidean open set allows the fundamental lemma for
smooth tests to detect its orthogonal complement.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Topology
open scoped ContDiff

namespace Riesz1.Internal

variable {Ω V E : Type*} [MeasurableSpace Ω]
  [AddCommGroup V] [Module ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Compact smooth tests in an almost-everywhere chart detect a scalar `L²` class. -/
theorem eq_zero_of_chart_tests (μ : Measure Ω) [IsFiniteMeasure μ]
    (s : Ω → E) (hs : MeasurableEmbedding s) (U : Set E) (hU : IsOpen U)
    (hμ : ∀ᵐ x ∂μ, s x ∈ U) (a : Lp ℝ 2 μ)
    (htest : ∀ g : E → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ U →
      ∫ x, g (s x) * a x ∂μ = 0) : a = 0 := by
  let A := (Lp.memLp a).aestronglyMeasurable.mk a
  let F := Function.extend s A (fun _ => (0 : ℝ))
  have hFs : ∀ x, F (s x) = A x := fun x => hs.injective.extend_apply _ _ x
  have hFa : (fun x => F (s x)) =ᵐ[μ] a := by
    simpa only [hFs] using (Lp.memLp a).aestronglyMeasurable.ae_eq_mk.symm
  have hFLp : MemLp F 2 (μ.map s) :=
    (hs.memLp_map_measure_iff).mpr ((Lp.memLp a).ae_eq hFa.symm)
  have hz : ∀ᵐ y ∂μ.map s, y ∈ U → F y = 0 := by
    apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((hFLp.integrable (by norm_num)).locallyIntegrable.locallyIntegrableOn U)
    intro g hg hgc hgU
    rw [hs.integral_map]
    convert htest g hg hgc hgU using 1
    apply integral_congr_ae
    filter_upwards [hFa] with x hx
    simp only [smul_eq_mul, hx]
  have hz' := hs.ae_map_iff.mp hz
  apply Lp.ext
  filter_upwards [hz', hμ, hFa, Lp.coeFn_zero ℝ 2 μ] with x hx hUx hFx h0x
  exact hFx.symm.trans ((hx hUx).trans h0x.symm)

/-- A family containing all smooth compact tests in an almost-everywhere
chart has dense range. The chart need not be continuous. -/
theorem denseRange_of_chart_tests (μ : Measure Ω) [IsFiniteMeasure μ]
    (j : V →ₗ[ℝ] Lp ℝ 2 μ) (s : Ω → E) (hs : MeasurableEmbedding s)
    (U : Set E) (hU : IsOpen U) (hμ : ∀ᵐ x ∂μ, s x ∈ U)
    (htest : ∀ g : E → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g → tsupport g ⊆ U →
      ∃ v : V, (j v : Ω → ℝ) =ᵐ[μ] g ∘ s) :
    DenseRange j := by
  have hbot : j.rangeᗮ = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    change a = 0
    apply eq_zero_of_chart_tests μ s hs U hU hμ a
    intro g hg hgc hgU
    obtain ⟨v, hv⟩ := htest g hg hgc hgU
    have hi : inner ℝ (j v) a = 0 := ha (j v) ⟨v, rfl⟩
    rw [L2.inner_def] at hi
    convert hi using 1
    apply integral_congr_ae
    filter_upwards [hv] with x hx
    simp only [Function.comp_apply, Real.inner_apply, hx]
  have htop : j.range.topologicalClosure = ⊤ := by
    apply Submodule.orthogonal_eq_bot_iff.mp
    rw [Submodule.orthogonal_closure, hbot]
  rw [denseRange_iff_closure_range]
  rw [← LinearMap.coe_range, ← Submodule.topologicalClosure_coe, htop]
  rfl

end Riesz1.Internal

end
