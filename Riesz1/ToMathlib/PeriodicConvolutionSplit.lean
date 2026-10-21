/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.KernelSplitDerivativeLocal
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Tactic

/-!
# Local near/far decompositions of periodic convolutions

A compactly supported near kernel can be integrated in displacement coordinates,
while the far kernel stays on a fixed period centered at the evaluation point.
The derivative falls on the input in the first integral and on the kernel in the
second. All integrability certificates and the coordinate changes are included.
This avoids integrating a nonintegrable kernel derivative at its singularity.
-/

public section

open MeasureTheory Set Filter Topology Metric

namespace Riesz1
namespace PeriodicConvolution

/-- A compact near kernel has the same convolution on a centered period and on
its fixed displacement support, provided that support stays inside the period. -/
theorem integral_near_eq {q N : ℝ → ℝ} {L a c x : ℝ}
    (hL : 0 < L) (ha : 0 ≤ a) (hx : |x - c| + a < L / 2)
    (hN : Function.support N ⊆ Ioc (-a) a) :
    (∫ y in Ioc (c - L / 2) (c + L / 2), q y * N (x - y)) =
      ∫ t in Ioc (-a) a, q (x - t) * N t := by
  have hs : Function.support (fun t => q (x - t) * N t) ⊆ Ioc (-a) a := by
    intro t ht
    exact hN (Function.mem_support.mpr (mul_ne_zero_iff.mp ht).2)
  have hs' : Function.support (fun t => q (x - t) * N t) ⊆
      Ioc (x - (c + L / 2)) (x - (c - L / 2)) := by
    intro t ht
    obtain ⟨ht0, ht1⟩ := hs ht
    have hx0 := neg_le_abs (x - c)
    have hx1 := le_abs_self (x - c)
    constructor <;> linarith
  rw [← intervalIntegral.integral_of_le (by linarith : c - L / 2 ≤ c + L / 2),
    ← intervalIntegral.integral_of_le (by linarith : -a ≤ a)]
  have he := intervalIntegral.integral_comp_sub_left
    (fun t => q (x - t) * N t) x (a := c - L / 2) (b := c + L / 2)
  simp only [sub_sub_cancel] at he
  rw [he, intervalIntegral.integral_eq_integral_of_support_subset hs',
    intervalIntegral.integral_eq_integral_of_support_subset hs]

/-- Periodic convolution integrands are periodic in the integration variable. -/
theorem integrand_periodic {q K : ℝ → ℝ} {L : ℝ}
    (hq : Function.Periodic q L) (hK : Function.Periodic K L) (x : ℝ) :
    Function.Periodic (fun y => q y * K (x - y)) L := by
  intro y
  dsimp only
  rw [hq y, show x - (y + L) = (x - y) - L by ring, hK.sub_eq]

/-- Moving the fundamental window does not change a periodic convolution. -/
theorem integral_window_eq {q K : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hq : Function.Periodic q L) (hK : Function.Periodic K L) (c x : ℝ) :
    (∫ y in Ioc (-(L / 2)) (L / 2), q y * K (x - y)) =
      ∫ y in Ioc (c - L / 2) (c + L / 2), q y * K (x - y) := by
  rw [← intervalIntegral.integral_of_le (by linarith : -(L / 2) ≤ L / 2),
    ← intervalIntegral.integral_of_le (by linarith : c - L / 2 ≤ c + L / 2)]
  convert (integrand_periodic hq hK x).intervalIntegral_add_eq (-(L / 2))
    (c - L / 2) using 1 <;> congr 1 <;> ring

/-- Local near/far differentiation of the actual periodic convolution. The
near kernel is supported in `(-a,a]`. The far kernel only needs regularity on
the displacements reached from the fixed centered period. All bounds here are
local hypotheses of this general analytic helper. -/
theorem hasDerivAt_split {q K N F : ℝ → ℝ} {L a c ε A B M : ℝ}
    (hL : 0 < L) (ha : 0 ≤ a) (hε : 0 < ε) (hroom : ε + a < L / 2)
    (hqp : Function.Periodic q L) (hKp : Function.Periodic K L)
    (hqm : Measurable q)
    (hqi : IntegrableOn q (Ioc (c - L / 2) (c + L / 2)))
    (hNi : IntegrableOn N (Ioc (-a) a))
    (hNs : Function.support N ⊆ Ioc (-a) a)
    (hFm : Measurable F)
    (hsplit : ∀ t, K t = N t + F t)
    (hqbound : ∀ x ∈ ball c ε, ∀ t ∈ Ioc (-a) a, |q (x - t)| ≤ A)
    (hqgood : ∀ x ∈ ball c ε, ∀ t ∈ Ioc (-a) a,
      DifferentiableAt ℝ q (x - t) ∧ |deriv q (x - t)| ≤ M)
    (hFbound : ∀ x ∈ ball c ε, ∀ y ∈ Ioc (c - L / 2) (c + L / 2),
      |F (x - y)| ≤ B)
    (hFgood : ∀ x ∈ ball c ε, ∀ y ∈ Ioc (c - L / 2) (c + L / 2),
      DifferentiableAt ℝ F (x - y) ∧ |deriv F (x - y)| ≤ B) :
    IntegrableOn (fun y => q y * K (c - y)) (Ioc (-(L / 2)) (L / 2)) ∧
    HasDerivAt (fun x => ∫ y in Ioc (-(L / 2)) (L / 2), q y * K (x - y))
      ((∫ t in Ioc (-a) a, deriv q (c - t) * N t) +
        ∫ y in Ioc (c - L / 2) (c + L / 2), q y * deriv F (c - y)) c := by
  have hnI (x : ℝ) (hx : x ∈ ball c ε) :
      IntegrableOn (fun t => q (x - t) * N t) (Ioc (-a) a) := by
    refine (hNi.norm.const_mul A).mono'
      (((hqm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable).mul
        hNi.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [norm_mul, Real.norm_eq_abs (q (x - t))]
    exact mul_le_mul_of_nonneg_right (hqbound x hx t ht) (norm_nonneg _)
  have hn := hasDerivAt_integral_comp_sub_mul measurableSet_Ioc hε hqm hNi
    (hnI c (mem_ball_self hε)) hqgood
  have hf := hasDerivAt_integral_mul_sub_local measurableSet_Ioc hε hqi hFm
    (hFbound c (mem_ball_self hε)) hFgood
  have hlocalI (x : ℝ) (hx : x ∈ ball c ε) :
      IntegrableOn (fun y => q y * N (x - y)) (Ioc (c - L / 2) (c + L / 2)) := by
    have hs : Function.support (fun t => q (x - t) * N t) ⊆ Ioc (-a) a := by
      intro t ht
      exact hNs (Function.mem_support.mpr (mul_ne_zero_iff.mp ht).2)
    have hglobal : Integrable (fun t => q (x - t) * N t) volume :=
      (integrableOn_iff_integrable_of_support_subset hs).mp (hnI x hx)
    simpa only [sub_sub_cancel] using (hglobal.comp_sub_left x).integrableOn
  have hfarI (x : ℝ) (hx : x ∈ ball c ε) : IntegrableOn
      (fun y => q y * F (x - y)) (Ioc (c - L / 2) (c + L / 2)) := by
    refine (hqi.norm.const_mul B).mono'
      (hqi.aestronglyMeasurable.mul
        ((hFm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    rw [norm_mul, Real.norm_eq_abs (F (x - y))]
    calc ‖q y‖ * |F (x - y)| ≤ ‖q y‖ * B :=
          mul_le_mul_of_nonneg_left (hFbound x hx y hy) (norm_nonneg _)
      _ = B * ‖q y‖ := mul_comm _ _
  have heq : (fun x => ∫ y in Ioc (-(L / 2)) (L / 2), q y * K (x - y)) =ᶠ[𝓝 c]
      (fun x => (∫ t in Ioc (-a) a, q (x - t) * N t) +
        ∫ y in Ioc (c - L / 2) (c + L / 2), q y * F (x - y)) := by
    filter_upwards [ball_mem_nhds c hε] with x hx
    rw [integral_window_eq hL hqp hKp c x]
    simp_rw [hsplit, mul_add]
    rw [integral_add (hlocalI x hx) (hfarI x hx), integral_near_eq hL ha ?_ hNs]
    have hx' : |x - c| < ε := by simpa only [mem_ball, Real.dist_eq] using hx
    linarith
  have hci : IntegrableOn (fun y => q y * K (c - y))
      (Ioc (c - L / 2) (c + L / 2)) := by
    apply ((hlocalI c (mem_ball_self hε)).add (hfarI c (mem_ball_self hε))).congr
    exact ae_of_all _ fun y => by dsimp; rw [hsplit]; ring
  have hperiodI : IntervalIntegrable (fun y => q y * K (c - y)) volume
      (c - L / 2) (c - L / 2 + L) := by
    rw [show c - L / 2 + L = c + L / 2 by ring]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mpr hci
  refine ⟨?_, (hn.add hf).congr_of_eventuallyEq heq⟩
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp
    ((integrand_periodic hqp hKp c).intervalIntegrable hL.ne' hperiodI _ _)

end PeriodicConvolution
end Riesz1
