/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.WeightedSobolev.LipschitzH1Convolution
public import Riesz1.ToMathlib.WeightedSobolev.GraphLimits
public import Riesz1.ToMathlib.WeightedSobolev.VariationalPairing
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Lipschitz functions in the weighted Sobolev completion

For a finite absolutely continuous measure carried by a bounded set, a function
locally Lipschitz near the closed set belongs to the weighted Sobolev completion,
with its classical almost everywhere gradient. No regularity of the density is needed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ContDiff NNReal

namespace Riesz1.WeightedSobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsFiniteMeasure μ] {U W : Set E} {F : E → ℝ} {C : ℝ≥0}

/-- Global Lipschitz functions belong to the weighted smooth completion. -/
theorem isWeightedH1_of_lipschitz (hU : Bornology.IsBounded U)
    (hμ : ∀ᵐ x ∂μ, x ∈ U) (hac : μ ≪ volume) (hF : LipschitzWith C F) :
    IsWeightedH1 μ U F (gradient F) := by
  obtain ⟨φ, hφ, hφb, hφgb, hφl, hφgl⟩ := exists_smooth_approximation_lipschitz hF
  have hFm : MemLp F 2 μ := memLp_of_continuousOn_closure hU hμ hF.continuous.continuousOn
  have hGm : MemLp (gradient F) 2 μ := by
    apply MemLp.of_bound
      ((InnerProductSpace.toDual ℝ E).symm.continuous.measurable.comp
        (measurable_fderiv ℝ F)).aestronglyMeasurable (C : ℝ)
    exact Eventually.of_forall fun x => by
      simpa only [Function.comp_def, gradient, LinearIsometryEquiv.norm_map] using
        (norm_fderiv_le_of_lipschitz ℝ hF (x₀ := x))
  have hm k : MemLp (φ k) 2 μ :=
    memLp_of_continuousOn_closure hU hμ (hφ k).continuous.continuousOn
  have hgm k : MemLp (gradient (φ k)) 2 μ := by
    apply MemLp.of_bound
      ((InnerProductSpace.toDual ℝ E).symm.continuous.measurable.comp
        (measurable_fderiv ℝ (φ k))).aestronglyMeasurable (C : ℝ)
    exact Eventually.of_forall (hφgb k)
  refine ⟨hFm, hGm, φ, fun k => ⟨univ, isOpen_univ, subset_univ _,
    (hφ k).contDiffOn⟩, ?_, ?_⟩
  · apply (tendsto_toLp_iff_lintegral_sq φ hm F hFm).mp
    apply tendsto_toLp_of_dominated hm hFm (hFm.norm.add (memLp_const (C : ℝ)))
      (fun k => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => le_add_of_nonneg_right C.coe_nonneg)
      (Eventually.of_forall hφl)
    calc
      ‖φ k x‖ = ‖(φ k x - F x) + F x‖ := by rw [sub_add_cancel]
      _ ≤ ‖φ k x - F x‖ + ‖F x‖ := norm_add_le _ _
      _ ≤ ‖F x‖ + C := by linarith [hφb k x]
  · apply (tendsto_toLp_iff_lintegral_sq _ hgm _ hGm).mp
    apply tendsto_toLp_of_dominated hgm hGm (memLp_const (C : ℝ))
      (fun k => Eventually.of_forall (hφgb k)) ?_ (hac.ae_le hφgl)
    exact Eventually.of_forall fun x => by
      simpa only [Function.comp_def, gradient, LinearIsometryEquiv.norm_map] using
        (norm_fderiv_le_of_lipschitz ℝ hF (x₀ := x))

/-- Lipschitz regularity is needed only on an open neighborhood of the closure.
The function can be completely arbitrary outside that neighborhood. -/
theorem isWeightedH1_of_lipschitzOn (hU : Bornology.IsBounded U)
    (hμ : ∀ᵐ x ∂μ, x ∈ U) (hac : μ ≪ volume)
    (hW : IsOpen W) (hUW : closure U ⊆ W) (hF : LipschitzOnWith C F W) :
    IsWeightedH1 μ U F (gradient F) := by
  obtain ⟨g, hg, hFg⟩ := hF.extend_real
  apply (isWeightedH1_of_lipschitz hU hμ hac hg).congr
  · filter_upwards [hμ] with x hx
    exact (hFg (hUW (subset_closure hx))).symm
  · filter_upwards [hμ] with x hx
    have he : F =ᶠ[𝓝 x] g := by
      filter_upwards [hW.mem_nhds (hUW (subset_closure hx))] with y hy
      exact hFg hy
    exact he.gradient_eq.symm

/-- Local Lipschitz regularity near the compact closure suffices. Compactness
supplies a single Lipschitz bound on a smaller neighborhood. -/
theorem isWeightedH1_of_locallyLipschitzOn (hU : Bornology.IsBounded U)
    (hμ : ∀ᵐ x ∂μ, x ∈ U) (hac : μ ≪ volume)
    (hW : IsOpen W) (hUW : closure U ⊆ W) (hF : LocallyLipschitzOn W F) :
    IsWeightedH1 μ U F (gradient F) := by
  obtain ⟨δ, hδ, hδW⟩ := hU.isCompact_closure.exists_cthickening_subset_open hW hUW
  have hK : IsCompact (cthickening δ (closure U)) := hU.isCompact_closure.cthickening
  obtain ⟨C, hC⟩ := (hF.mono hδW).exists_lipschitzOnWith_of_compact hK
  exact isWeightedH1_of_lipschitzOn hU hμ hac isOpen_thickening
    (self_subset_thickening hδ _) (hC.mono (thickening_subset_cthickening _ _))

end Riesz1.WeightedSobolev

end
