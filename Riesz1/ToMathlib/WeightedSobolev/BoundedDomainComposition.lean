/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.WeightedSobolev.CompositionLimits
public import Riesz1.ToMathlib.WeightedSobolev.SmoothCompositionAE
public import Riesz1.ToMathlib.WeightedSobolev.VariationalPairing

/-!
# Scalar composition on bounded Euclidean Sobolev completions

The smooth and `C¹` chain rules hold for every finite measure carried
by a bounded domain, even before gradient uniqueness is known.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ContDiff NNReal

namespace Riesz1.WeightedSobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsFiniteMeasure μ] {U : Set E}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Smooth scalar composition preserves the defining smooth core. -/
theorem SmoothNearClosure.comp_smooth {f : E → ℝ} (hf : SmoothNearClosure U f)
    {T : ℝ → ℝ} (hT : ContDiff ℝ ∞ T) : SmoothNearClosure U (T ∘ f) := by
  obtain ⟨W, hW, hUW, hfW⟩ := hf
  exact ⟨W, hW, hUW, hT.comp_contDiffOn hfW⟩

/-- Smooth composition in the completed graph over a bounded domain. -/
theorem IsWeightedH1.comp_smooth (hU : Bornology.IsBounded U)
    (hμ : ∀ᵐ x ∂μ, x ∈ U) {F : E → ℝ} {G : E → E}
    (hFG : IsWeightedH1 μ U F G) {T : ℝ → ℝ} (hT : ContDiff ℝ ∞ T)
    (h0 : T 0 = 0) {C : ℝ≥0} (hb : ∀ r, ‖deriv T r‖₊ ≤ C) :
    IsWeightedH1 μ U (fun x => T (F x)) (fun x => deriv T (F x) • G x) := by
  apply Internal.graph_comp_smooth_ae (P := SmoothNearClosure U) (value := id) (grad := gradient)
    (fun f hf => (memLp_of_smoothNearClosure hU hμ hf).1)
    (fun f hf => (memLp_of_smoothNearClosure hU hμ hf).2)
    hT h0 hb (fun f => T ∘ f) (fun f hf => hf.comp_smooth hT)
    (fun _ _ _ => rfl) ?_ hFG
  intro f hf
  obtain ⟨W, hW, hUW, hfW⟩ := hf
  filter_upwards [hμ] with x hx
  have hdf := (hfW.differentiableOn (by norm_num)).differentiableAt
    (hW.mem_nhds (hUW (subset_closure hx)))
  have hdT := (hT.differentiable (by norm_num) (f x)).hasDerivAt
  have he := (hdT.comp_hasFDerivAt x hdf.hasFDerivAt).fderiv
  change (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (T ∘ f) x) = _
  rw [he, map_smul]
  rfl

/-- The `C¹` bounded-derivative chain rule in a bounded-domain completion. -/
theorem IsWeightedH1.comp_C1 (hU : Bornology.IsBounded U)
    (hμ : ∀ᵐ x ∂μ, x ∈ U) {F : E → ℝ} {G : E → E}
    (hFG : IsWeightedH1 μ U F G) {T : ℝ → ℝ} (hT : ContDiff ℝ 1 T)
    (h0 : T 0 = 0) {C : ℝ≥0} (hb : ∀ r, ‖deriv T r‖₊ ≤ C) :
    IsWeightedH1 μ U (fun x => T (F x)) (fun x => deriv T (F x) • G x) := by
  exact Internal.graph_comp_C1 (P := SmoothNearClosure U) (value := id) (grad := gradient)
    (fun f hf => (memLp_of_smoothNearClosure hU hμ hf).1)
    (fun f hf => (memLp_of_smoothNearClosure hU hμ hf).2)
    hFG.1 hFG.2.1 (fun _ hS hS0 _ hSb => hFG.comp_smooth hU hμ hS hS0 hSb)
    hT h0 hb

end Riesz1.WeightedSobolev

end
