/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.LoopForce
public import Riesz1.Kernel.MeanFieldEnergyFourier
public import Riesz1.Kernel.Coefficients
public import Riesz1.ToMathlib.HeatKernel.OperatorsHeat
import all Riesz1.Variance.LoopForceKernel

/-!
# Convolution cancellation for the transport

Analytic steps in the proof of Proposition 5.5.
Integration by parts turns the symmetric principal value `g' * ψ` into the
absolutely convergent convolution `g * ψ'`.
-/

public section

open MeasureTheory Set Filter Topology Complex
open scoped ContDiff Real

namespace Riesz1

/-- Moving the derivative from the Riesz kernel to a smooth periodic field. -/
theorem pvConv_eq_integral_deriv {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hp : Function.Periodic ψ 1) (x : ℝ) :
    pvConv s ψ x = ∫ u in (0 : ℝ)..1, hurwitzKernel s u * deriv ψ (x - u) := by
  have hdc : Continuous (deriv ψ) := hψ.continuous_deriv (by simp)
  have hi := integrableOn_kernel_mul s hs0 hs1 (fun u => deriv ψ (x - u))
    (hdc.comp (continuous_const.sub continuous_id))
  have hpart (h : ℝ) (h0 : 0 < h) (h1 : h < 1 / 4) :
      (∫ u in h..(1 - h), deriv (hurwitzKernel s) u * ψ (x - u)) =
        hurwitzKernel s h * (ψ (x + h) - ψ (x - h)) +
          ∫ u in h..(1 - h), hurwitzKernel s u * deriv ψ (x - u) := by
    have hmem : ∀ u ∈ uIcc h (1 - h), (u : UnitAddCircle) ≠ 0 := by
      intro u hu
      rw [uIcc_of_le (by linarith)] at hu
      exact coe_ne_zero_of_mem_Ioo01 (by linarith [hu.1]) (by linarith [hu.2])
    have hgd : ∀ u ∈ uIcc h (1 - h),
        HasDerivAt (hurwitzKernel s) (deriv (hurwitzKernel s) u) u :=
      fun u hu => (differentiableAt_hurwitzKernel_of_ne s hs0 hs1 u (hmem u hu)).hasDerivAt
    have hpd (u : ℝ) : HasDerivAt (fun v => ψ (x - v)) (-deriv ψ (x - u)) u := by
      convert ((hψ.differentiable (by simp) (x - u)).hasDerivAt.comp u
        ((hasDerivAt_id u).const_sub x)) using 1
      · rfl
      · ring
    have hGint : IntervalIntegrable (deriv (hurwitzKernel s)) volume h (1 - h) := by
      apply ContinuousOn.intervalIntegrable
      exact fun u hu => (continuousAt_deriv_hurwitzKernel hs0 hs1 (hmem u hu)).continuousWithinAt
    have hPint : IntervalIntegrable (fun u => -deriv ψ (x - u)) volume h (1 - h) :=
      ((hdc.comp (continuous_const.sub continuous_id)).neg).intervalIntegrable _ _
    have he := intervalIntegral.integral_mul_deriv_eq_deriv_mul hgd
      (fun u _ => hpd u) hGint hPint
    have hg : hurwitzKernel s (1 - h) = hurwitzKernel s h := by
      rw [show 1 - h = -h + 1 by ring, hurwitzKernel_add_one, hurwitzKernel_neg]
    have hshift : ψ (x - (1 - h)) = ψ (x + h) := by
      rw [show x - (1 - h) = x + h - 1 by ring, hp.sub_eq]
    have hn : (∫ u in h..(1 - h), hurwitzKernel s u * -deriv ψ (x - u)) =
        -(∫ u in h..(1 - h), hurwitzKernel s u * deriv ψ (x - u)) := by
      simp only [mul_neg, intervalIntegral.integral_neg]
    rw [hg, hshift, hn] at he
    linarith
  obtain ⟨C, hC⟩ := hurwitzKernel_small s hs0 hs1
  obtain ⟨M, hM0, hM⟩ := exists_abs_sub_le_dist hψ hp
  have hbound : Tendsto (fun h : ℝ => hurwitzKernel s h * (ψ (x + h) - ψ (x - h)))
      (𝓝[>] 0) (𝓝 0) := by
    have hpow : Tendsto (fun h : ℝ => h ^ (1 - s)) (𝓝[>] 0) (𝓝 0) := by
      have ht := (Real.continuousAt_rpow_const 0 (1 - s) (Or.inr (by linarith))).tendsto
      rw [Real.zero_rpow (by linarith : (1 - s) ≠ 0)] at ht
      exact ht.mono_left nhdsWithin_le_nhds
    have ht : Tendsto (fun h : ℝ => 2 * (|C| * M) * h ^ (1 - s)) (𝓝[>] 0) (𝓝 0) := by
      simpa using hpow.const_mul (2 * (|C| * M))
    refine squeeze_zero_norm' ?_ ht
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 8)] with h hh
    have hd : dist ((2 * h : ℝ) : UnitAddCircle) 0 = 2 * h :=
      dist_coe_zero_of_mem_Ico (by linarith [hh.1]) (by linarith [hh.2])
    have hdiff : |ψ (x + h) - ψ (x - h)| ≤ M * (2 * h) := by
      have hb := hM (x - h) (2 * h)
      rwa [show x - h + 2 * h = x + h by ring, hd] at hb
    have hker : |hurwitzKernel s h| ≤ |C| * h ^ (-s) :=
      (hC h hh.1 (by linarith [hh.2])).trans
        (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg hh.1.le _))
    have he : h ^ (-s) * h = h ^ (1 - s) := by
      calc h ^ (-s) * h = h ^ (-s) * h ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = h ^ (1 - s) := by rw [← Real.rpow_add hh.1]; congr 1; ring
    rw [Real.norm_eq_abs, abs_mul]
    calc |hurwitzKernel s h| * |ψ (x + h) - ψ (x - h)|
        ≤ (|C| * h ^ (-s)) * (M * (2 * h)) :=
          mul_le_mul hker hdiff (abs_nonneg _)
            (mul_nonneg (abs_nonneg C) (Real.rpow_nonneg hh.1.le _))
      _ = 2 * (|C| * M) * (h ^ (-s) * h) := by ring
      _ = 2 * (|C| * M) * h ^ (1 - s) := by rw [he]
  have ht := (hbound.add (tendsto_interval_shrink _ hi)).congr'
    (show (fun h : ℝ => ∫ u in h..(1 - h), deriv (hurwitzKernel s) u * ψ (x - u)) =ᶠ[𝓝[>] 0]
      (fun h : ℝ => hurwitzKernel s h * (ψ (x + h) - ψ (x - h)) +
        ∫ u in h..(1 - h), hurwitzKernel s u * deriv ψ (x - u)) from by
      filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4)] with h hh
      exact hpart h hh.1 hh.2).symm
  rw [zero_add] at ht
  have hpv := tendsto_truncated_pv hs0 hs1 hψ hp x
  rw [← pvConv_eq hs0 hs1 hψ hp x] at hpv
  exact tendsto_nhds_unique hpv ht

end Riesz1

end
