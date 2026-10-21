/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.WeightedSobolev.Graph
public import Riesz1.ToMathlib.WeightedSobolev.L2Facts
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Slicing a completed first-order graph

Convergence of jets on a product has a subsequence converging in the slice norm almost
everywhere. This gives Sobolev slicing directly from the defining smooth approximation,
without restricting a measurable representative to a prescribed null slice. Used in the
rotation step of Lemma 3.9.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Riesz1.WeightedSobolev

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [NormedAddCommGroup E] {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]

omit [SFinite μ] in
/-- Almost everywhere equality of measurable slices gives equality on the product. -/
theorem ae_eq_prod_of_ae_eq_slices {F G : α × β → E}
    (hF : AEStronglyMeasurable F (μ.prod ν))
    (hG : AEStronglyMeasurable G (μ.prod ν))
    (h : ∀ᵐ x ∂μ, (fun y => F (x, y)) =ᵐ[ν] (fun y => G (x, y))) :
    F =ᵐ[μ.prod ν] G := by
  have hm : AEMeasurable (fun p => ‖F p - G p‖ₑ) (μ.prod ν) := (hF.sub hG).enorm
  have hz : (∫⁻ p, ‖F p - G p‖ₑ ∂μ.prod ν) = 0 := by
    rw [lintegral_prod _ hm]
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [h] with x hx
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [hx] with y hy
    change F (x, y) = G (x, y) at hy
    simp only [hy, sub_self, enorm_zero, Pi.zero_apply]
  filter_upwards [(lintegral_eq_zero_iff' hm).mp hz] with p hp
  exact sub_eq_zero.mp (enorm_eq_zero.mp hp)

/-- Square-integrability on a product implies square-integrability on almost every slice. -/
theorem ae_memLp_prod_right {F : α × β → E} (hF : MemLp F 2 (μ.prod ν)) :
    ∀ᵐ x ∂μ, MemLp (fun y => F (x, y)) 2 ν := by
  have hi := (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mp hF
  filter_upwards [hF.aestronglyMeasurable.prodMk_left, hi.prod_right_ae] with x hm hx
  exact (memLp_two_iff_integrable_sq_norm hm).mpr hx

/-- A sequence tending to zero in the product `L²` norm has a subsequence tending to
zero in almost every slice `L²` norm. The integral formulation avoids choosing slice
representatives in an `Lp` space. -/
theorem exists_subsequence_ae_tendsto_slice_norm_sq {f : ℕ → α × β → E}
    (hf : ∀ k, MemLp (f k) 2 (μ.prod ν))
    (hlim : Tendsto (fun k => ∫ p, ‖f k p‖ ^ 2 ∂μ.prod ν) atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ x ∂μ, Tendsto (fun k => ∫ y, ‖f (ns k) (x, y)‖ ^ 2 ∂ν) atTop (𝓝 0) := by
  let J : ℕ → α → ℝ := fun k x => ∫ y, ‖f k (x, y)‖ ^ 2 ∂ν
  have hi (k : ℕ) : Integrable (fun p => ‖f k p‖ ^ 2) (μ.prod ν) :=
    (memLp_two_iff_integrable_sq_norm (hf k).aestronglyMeasurable).mp (hf k)
  have hJ (k : ℕ) : Integrable (J k) μ := (hi k).integral_prod_left
  have hJ0 (k : ℕ) (x : α) : 0 ≤ J k x := integral_nonneg fun _ => sq_nonneg _
  have hnorm (k : ℕ) : eLpNorm (J k - 0) 1 μ =
      ENNReal.ofReal (∫ p, ‖f k p‖ ^ 2 ∂μ.prod ν) := by
    simp only [sub_zero]
    rw [eLpNorm_one_eq_lintegral_enorm (hJ k).aestronglyMeasurable]
    have he : (fun x => ‖J k x‖ₑ) = (fun x => ENNReal.ofReal (J k x)) := by
      funext x
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hJ0 k x)]
    rw [he, ← ofReal_integral_eq_lintegral_ofReal (hJ k)
      (Eventually.of_forall (hJ0 k)), ← integral_prod _ (hi k)]
  have ht : Tendsto (fun k => eLpNorm (J k - 0) 1 μ) atTop (𝓝 0) := by
    simp only [hnorm]
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim
  exact (tendstoInMeasure_of_tendsto_eLpNorm (by simp : (1 : ℝ≥0∞) ≠ 0) ht).exists_seq_tendsto_ae

omit [SFinite ν] in
private theorem ofReal_integral_norm_sq {f : β → E} (hf : MemLp f 2 ν) :
    ENNReal.ofReal (∫ y, ‖f y‖ ^ 2 ∂ν) = ∫⁻ y, ‖f y‖ₑ ^ 2 ∂ν := by
  rw [ofReal_integral_eq_lintegral_ofReal
    ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf)
    (Eventually.of_forall fun _ => sq_nonneg _)]
  exact lintegral_congr fun _ => (enorm_sq_eq_ofReal_norm_sq _).symm

/-- Slicing the closure of a graph. The slice test family can depend on the first
coordinate. Both limiting components and the same subsequence of tests are retained. -/
theorem IsGraphH1.ae_slice {T : Type*} {P : T → Prop}
    {value : T → α × β → ℝ} {derivative : T → α × β → E}
    {F : α × β → ℝ} {G : α × β → E}
    (h : IsGraphH1 (μ.prod ν) P value derivative F G)
    (hv : ∀ t, P t → MemLp (value t) 2 (μ.prod ν))
    (hg : ∀ t, P t → MemLp (derivative t) 2 (μ.prod ν)) :
    ∀ᵐ x ∂μ, IsGraphH1 ν P
      (fun t y => value t (x, y)) (fun t y => derivative t (x, y))
      (fun y => F (x, y)) (fun y => G (x, y)) := by
  obtain ⟨hF, hG, φ, hφ, hφv, hφg⟩ := h
  have hvlim := tendsto_integral_norm_sq_of_lintegral
    (fun k => ((hv _ (hφ k)).sub hF).aestronglyMeasurable) hφv
  have hglim := tendsto_integral_norm_sq_of_lintegral
    (fun k => ((hg _ (hφ k)).sub hG).aestronglyMeasurable) hφg
  obtain ⟨ns, hns, hnv⟩ := exists_subsequence_ae_tendsto_slice_norm_sq
    (fun k => (hv _ (hφ k)).sub hF) hvlim
  obtain ⟨ms, hms, hmg⟩ := exists_subsequence_ae_tendsto_slice_norm_sq
    (fun k => (hg _ (hφ (ns k))).sub hG) (hglim.comp hns.tendsto_atTop)
  have hvsl : ∀ᵐ x ∂μ, ∀ k, MemLp (fun y => value (φ k) (x, y)) 2 ν :=
    ae_all_iff.mpr fun k => ae_memLp_prod_right (hv _ (hφ k))
  have hgsl : ∀ᵐ x ∂μ, ∀ k, MemLp (fun y => derivative (φ k) (x, y)) 2 ν :=
    ae_all_iff.mpr fun k => ae_memLp_prod_right (hg _ (hφ k))
  filter_upwards [ae_memLp_prod_right hF, ae_memLp_prod_right hG, hvsl, hgsl, hnv, hmg]
    with x hxF hxG hxv hxg hxnv hxmg
  refine ⟨hxF, hxG, fun k => φ (ns (ms k)), fun k => hφ _, ?_, ?_⟩
  · have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (hxnv.comp hms.tendsto_atTop)
    simp only [Function.comp_def, ENNReal.ofReal_zero, Pi.sub_apply] at ht
    convert ht using 1
    funext k
    exact (ofReal_integral_norm_sq ((hxv _).sub hxF)).symm
  · have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hxmg
    simp only [Function.comp_def, ENNReal.ofReal_zero, Pi.sub_apply] at ht
    convert ht using 1
    funext k
    exact (ofReal_integral_norm_sq ((hxg _).sub hxG)).symm

end Riesz1.WeightedSobolev

end
