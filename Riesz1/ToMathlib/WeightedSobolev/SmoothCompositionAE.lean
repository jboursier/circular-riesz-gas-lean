/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.WeightedSobolev.SmoothComposition
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Smooth composition with an almost everywhere core chain rule

An internal graph theorem separates the nonlinear limit from the
geometric fact that a smooth core is closed under smooth composition.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ContDiff NNReal

namespace Riesz1.WeightedSobolev.Internal

variable {Ω J E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure Ω} {P : J → Prop} {value : J → Ω → ℝ} {grad : J → Ω → E}

/-- Smooth composition for any finite-norm core stable under its classical chain rule. -/
theorem graph_comp_smooth_ae (hv : ∀ t, P t → MemLp (value t) 2 μ)
    (hg : ∀ t, P t → MemLp (grad t) 2 μ)
    {T : ℝ → ℝ} (hT : ContDiff ℝ ∞ T) (h0 : T 0 = 0) {C : ℝ≥0}
    (hb : ∀ r, ‖deriv T r‖₊ ≤ C) (comp : J → J)
    (hcomp : ∀ t, P t → P (comp t))
    (hval : ∀ t, P t → ∀ x, value (comp t) x = T (value t x))
    (hgrad : ∀ t, P t → grad (comp t) =ᵐ[μ] fun x => deriv T (value t x) • grad t x)
    {F : Ω → ℝ} {G : Ω → E} (hFG : IsGraphH1 μ P value grad F G) :
    IsGraphH1 μ P value grad (fun x => T (F x)) (fun x => deriv T (F x) • G x) := by
  obtain ⟨hF, hG, φ, hφ, hφv, hφg⟩ := hFG
  have hLip := lipschitzWith_of_nnnorm_deriv_le (hT.differentiable (by norm_num)) hb
  have hd : Continuous (deriv T) := hT.continuous_deriv (by simp)
  have hbd r : ‖deriv T r‖ ≤ (C : ℝ) := hb r
  have hTF := hLip.comp_memLp h0 hF
  have hdG := memLp_bounded_comp_smul hd hbd hF.aestronglyMeasurable hG
  have hvl := (tendsto_toLp_iff_lintegral_sq (fun k => value (φ k))
    (fun k => hv _ (hφ k)) F hF).mpr hφv
  obtain ⟨ns, hns, hnsLim⟩ := (tendstoInMeasure_of_tendsto_Lp hvl).exists_seq_tendsto_ae
  have hae : ∀ᵐ x ∂μ, Tendsto (fun k => value (φ (ns k)) x) atTop (𝓝 (F x)) := by
    filter_upwards [hnsLim, ae_all_iff.mpr (fun k => (hv _ (hφ k)).coeFn_toLp),
      hF.coeFn_toLp] with x hx hφx hFx
    simpa only [hφx, hFx] using hx
  have hder := tendsto_bounded_comp_smul hd hbd hF.aestronglyMeasurable
    (fun k => (hv _ (hφ (ns k))).aestronglyMeasurable) hae hG
    (fun k => hg _ (hφ (ns k))) (hφg.comp hns.tendsto_atTop)
  have hcompLp k : (hv (comp (φ (ns k))) (hcomp _ (hφ (ns k)))).toLp
      (value (comp (φ (ns k)))) = hLip.compLp h0 ((hv _ (hφ (ns k))).toLp (value (φ (ns k)))) := by
    apply Lp.ext
    filter_upwards [(hv _ (hcomp _ (hφ (ns k)))).coeFn_toLp,
      hLip.coeFn_compLp h0 ((hv _ (hφ (ns k))).toLp _), (hv _ (hφ (ns k))).coeFn_toLp]
      with x hx hcompLp hφx
    rw [hx, hcompLp]
    simp only [Function.comp_def]
    rw [hφx, hval _ (hφ (ns k))]
  have hlimitLp : hTF.toLp (fun x => T (F x)) = hLip.compLp h0 (hF.toLp F) := by
    apply Lp.ext
    filter_upwards [hTF.coeFn_toLp, hLip.coeFn_compLp h0 (hF.toLp F), hF.coeFn_toLp]
      with x hx hy hFx
    change (hTF.toLp (T ∘ F) : Ω → ℝ) x = _
    rw [hx, hy]
    simp only [Function.comp_def]
    rw [hFx]
  have hvalueLim : Tendsto (fun k => (hv _ (hcomp _ (hφ (ns k)))).toLp
      (value (comp (φ (ns k))))) atTop (𝓝 (hTF.toLp (fun x => T (F x)))) := by
    simp only [hcompLp, hlimitLp]
    exact (hLip.continuous_compLp h0).continuousAt.tendsto.comp (hvl.comp hns.tendsto_atTop)
  refine ⟨hTF, hdG, fun k => comp (φ (ns k)), fun k => hcomp _ (hφ (ns k)), ?_, ?_⟩
  · exact (tendsto_toLp_iff_lintegral_sq _ (fun k => hv _ (hcomp _ (hφ (ns k)))) _ hTF).mp hvalueLim
  · apply hder.congr
    intro k
    apply lintegral_congr_ae
    filter_upwards [hgrad (φ (ns k)) (hφ (ns k))] with x hx
    rw [hx]

end Riesz1.WeightedSobolev.Internal

end
