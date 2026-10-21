/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.LoopScale
import all Riesz1.Variance.LoopForce
import all Riesz1.Variance.LoopForceKernel

/-!
# Absolute convergence on the Lipschitz carrier of the scaled loop

The background terms of the loop functional converge for every Lipschitz
profile, including profiles that are not smooth.
-/

public section

open MeasureTheory Set Filter Topology

namespace Riesz1

lemma loopScaleField_lipschitz {ℓ : ℝ} (ψ : LoopScaleProfile ℓ) :
    ∃ C : NNReal, LipschitzWith C (loopScaleField ℓ ψ.val) := by
  obtain ⟨C, hC⟩ := ψ.property.2
  have hd : LipschitzWith ‖ℓ⁻¹‖₊ (fun u : ℝ => u / ℓ) := by
    simpa only [div_eq_inv_mul, smul_eq_mul] using (lipschitzWith_smul ℓ⁻¹ :
      LipschitzWith ‖ℓ⁻¹‖₊ (fun u : ℝ => ℓ⁻¹ • u))
  exact ⟨_, (lipschitzWith_smul ℓ).comp (hC.comp hd)⟩

lemma loopScale_lipschitz_increment {f : ℝ → ℝ} {C : NNReal} (hf : LipschitzWith C f)
    (hp : Function.Periodic f 1) (a t : ℝ) :
    |f (a + t) - f a| ≤ (C : ℝ) * dist (t : UnitAddCircle) 0 := by
  have hn : f (a + t) = f (a + (t - round t)) := by
    have h := (hp.int_mul (round t)) (a + (t - round t))
    rwa [show a + (t - round t) + (round t : ℝ) * 1 = a + t by ring] at h
  rw [hn, dist_coe_zero_eq]
  have h := hf.norm_sub_le (a + (t - round t)) a
  simpa only [Real.norm_eq_abs, add_sub_cancel_left] using h

lemma loopScale_abs_pvIntegrand_le (s : RieszExponent) {f : ℝ → ℝ} {M : NNReal}
    (hf : LipschitzWith M f) (hp : Function.Periodic f 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x u : ℝ, 0 < u → u < 1 →
      |pvIntegrand s.val f x u| ≤ K * (u ^ (-s.val) + (1 - u) ^ (-s.val)) := by
  obtain ⟨C, hC, hgb⟩ := deriv_hurwitzKernel_bound s.val s.property.1 s.property.2
  refine ⟨C * M, mul_nonneg hC.le M.property, fun x u h0 h1 => ?_⟩
  have hne : (u : UnitAddCircle) ≠ 0 := coe_ne_zero_of_mem_Ioo01 h0 h1
  have hd : 0 < dist (u : UnitAddCircle) 0 := dist_pos.mpr hne
  have hψ : |f (x - u) - f x| ≤ (M : ℝ) * dist (u : UnitAddCircle) 0 := by
    have h := loopScale_lipschitz_increment hf hp x (-u)
    simpa only [← sub_eq_add_neg, AddCircle.coe_neg, dist_zero_right, norm_neg] using h
  have he : dist (u : UnitAddCircle) 0 ^ (-s.val - 1) * dist (u : UnitAddCircle) 0 =
      dist (u : UnitAddCircle) 0 ^ (-s.val) := by
    rw [Real.rpow_sub_one hd.ne', div_mul_cancel₀ _ hd.ne']
  unfold pvIntegrand
  rw [abs_mul]
  calc |deriv (hurwitzKernel s.val) u| * |f (x - u) - f x|
      ≤ (C * dist (u : UnitAddCircle) 0 ^ (-s.val - 1)) *
        ((M : ℝ) * dist (u : UnitAddCircle) 0) :=
          mul_le_mul (hgb u hne) hψ (abs_nonneg _)
            (mul_nonneg hC.le (Real.rpow_nonneg (dist_nonneg) _))
    _ = (C * M) * dist (u : UnitAddCircle) 0 ^ (-s.val) := by
      calc _ = (C * M) * (dist (u : UnitAddCircle) 0 ^ (-s.val - 1) *
          dist (u : UnitAddCircle) 0) := by ring
        _ = _ := by rw [he]
    _ ≤ (C * M) * (u ^ (-s.val) + (1 - u) ^ (-s.val)) :=
      mul_le_mul_of_nonneg_left (dist_rpow_le_majorant h0 h1) (mul_nonneg hC.le M.property)

lemma loopScale_intervalIntegrable_pvIntegrand (s : RieszExponent) {f : ℝ → ℝ} {M : NNReal}
    (hf : LipschitzWith M f) (hp : Function.Periodic f 1) (x : ℝ) :
    IntervalIntegrable (pvIntegrand s.val f x) volume 0 1 := by
  obtain ⟨K, _, hK⟩ := loopScale_abs_pvIntegrand_le s hf hp
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
  refine Integrable.mono' ((integrableOn_rpow_majorant s.property.2).const_mul K)
    ((measurable_pvIntegrand s.val hf.continuous).comp measurable_prodMk_left).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  rw [Real.norm_eq_abs]
  exact hK x u hu.1 hu.2

/-- Each particle-background integral in the loop is absolutely convergent for Lipschitz tests. -/
theorem loopScale_intervalIntegrable_kernel_right (s : RieszExponent) {f : ℝ → ℝ} {M : NNReal}
    (hf : LipschitzWith M f) (hp : Function.Periodic f 1) (x : ℝ) :
    IntervalIntegrable (fun y => loopKernel s.val f x y) volume 0 1 := by
  have hpv : Function.Periodic (pvIntegrand s.val f x) 1 := by
    intro u
    unfold pvIntegrand
    rw [deriv_hurwitzKernel_add_one', show x - (u + 1) = (x - u) - 1 by ring, hp.sub_eq]
  have hi := hpv.intervalIntegrable (t := 0) one_ne_zero
    (by simpa only [zero_add] using loopScale_intervalIntegrable_pvIntegrand s hf hp x) (x - 1) x
  have hc := hi.comp_sub_left x
  rw [show x - (x - 1) = 1 by ring, sub_self] at hc
  refine hc.symm.neg.congr (fun y _ => ?_)
  change -pvIntegrand s.val f x (x - y) = loopKernel s.val f x y
  unfold loopKernel pvIntegrand
  rw [sub_sub_cancel]
  ring

lemma loopScale_kernel_symm (s : ℝ) (f : ℝ → ℝ) (a b : ℝ) :
    loopKernel s f a b = loopKernel s f b a := by
  unfold loopKernel
  have h := deriv_hurwitzKernel_neg' s (a - b)
  rw [show -(a - b) = b - a by ring] at h
  rw [h]
  ring

theorem loopScale_intervalIntegrable_kernel_left (s : RieszExponent) {f : ℝ → ℝ} {M : NNReal}
    (hf : LipschitzWith M f) (hp : Function.Periodic f 1) (y : ℝ) :
    IntervalIntegrable (fun x => loopKernel s.val f x y) volume 0 1 := by
  simp_rw [loopScale_kernel_symm s.val f _ y]
  exact loopScale_intervalIntegrable_kernel_right s hf hp y

lemma loopScale_integrable_pvIntegrand_prod (s : RieszExponent) {f : ℝ → ℝ} {M : NNReal}
    (hf : LipschitzWith M f) (hp : Function.Periodic f 1) :
    Integrable (fun p : ℝ × ℝ => pvIntegrand s.val f p.1 p.2)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  obtain ⟨K, _, hK⟩ := loopScale_abs_pvIntegrand_le s hf hp
  have hc : Integrable (fun _ : ℝ => K) (volume.restrict (Ioo (0 : ℝ) 1)) :=
    integrableOn_const measure_Ioo_lt_top.ne
  refine Integrable.mono' (hc.mul_prod (integrableOn_rpow_majorant s.property.2))
    (measurable_pvIntegrand s.val hf.continuous).aestronglyMeasurable ?_
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with p hp'
  rw [Real.norm_eq_abs]
  exact hK p.1 p.2 hp'.2.1 hp'.2.2

lemma loopScale_integral_kernel_eq (s : ℝ) {f : ℝ → ℝ} (hp : Function.Periodic f 1) (x : ℝ) :
    (∫ y in (0 : ℝ)..1, loopKernel s f x y) =
      -(∫ u in (0 : ℝ)..1, pvIntegrand s f x u) := by
  have he (y : ℝ) : loopKernel s f x y = -pvIntegrand s f x (x - y) := by
    unfold loopKernel pvIntegrand
    rw [sub_sub_cancel]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_comp_sub_left, sub_zero]
  congr 1
  have hpv : Function.Periodic (pvIntegrand s f x) 1 := by
    intro u
    unfold pvIntegrand
    rw [deriv_hurwitzKernel_add_one', show x - (u + 1) = (x - u) - 1 by ring, hp.sub_eq]
  have ht := hpv.intervalIntegral_add_eq (x - 1) 0
  simpa only [sub_add_cancel, zero_add] using ht

/-- The background-background iterated integral is an integral of an integrable function,
on the full Lipschitz carrier of the definition. -/
theorem loopScale_intervalIntegrable_background (s : RieszExponent) {f : ℝ → ℝ} {M : NNReal}
    (hf : LipschitzWith M f) (hp : Function.Periodic f 1) :
    IntervalIntegrable (fun x => ∫ y in (0 : ℝ)..1, loopKernel s.val f x y) volume 0 1 := by
  simp_rw [loopScale_integral_kernel_eq s.val hp]
  apply IntervalIntegrable.neg
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
  have hi := (loopScale_integrable_pvIntegrand_prod s hf hp).integral_prod_left
  refine hi.congr (Eventually.of_forall fun x => ?_)
  change (∫ y in Ioo (0 : ℝ) 1, pvIntegrand s.val f x y) =
    ∫ u in (0 : ℝ)..1, pvIntegrand s.val f x u
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]

/-- Every background integral in `loopScale` converges absolutely for every profile
in its carrier. No smoothness assumption is imposed. -/
theorem loopScale_background_integrals (s : RieszExponent) (ℓ : Ioc (0 : ℝ) 1)
    (ψ : LoopScaleProfile ℓ.val) :
    (∀ x, IntervalIntegrable (fun y => loopKernel s.val (loopScaleField ℓ.val ψ.val) x y) volume 0 1) ∧
    (∀ y, IntervalIntegrable (fun x => loopKernel s.val (loopScaleField ℓ.val ψ.val) x y) volume 0 1) ∧
    IntervalIntegrable (fun x => ∫ y in (0 : ℝ)..1,
      loopKernel s.val (loopScaleField ℓ.val ψ.val) x y) volume 0 1 := by
  obtain ⟨C, hC⟩ := loopScaleField_lipschitz ψ
  have hp := loopScaleField_periodic ψ.property.1
  exact ⟨loopScale_intervalIntegrable_kernel_right s hC hp,
    loopScale_intervalIntegrable_kernel_left s hC hp, loopScale_intervalIntegrable_background s hC hp⟩

end Riesz1

end
