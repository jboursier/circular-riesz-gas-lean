/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.InterchangeSummable
public import Riesz1.ToMathlib.HeatKernel.Circle
public import Mathlib.Tactic

/-!
# The heat kernel as a sum of interchange integrands

The periodized Gaussian formula `W_t(x) = (4πt)^{-1/2} ∑_k e^{-(x-k)²/(4t)}` of equation (2.7)
and the normalization `∫_0^1 W_t = 1` give `∑_k A_k(t) = √(4πt)` for the averages `A_k(t)` of
Lemma 2.1. Subtracting this from the periodized Gaussian formula writes the
heat kernel minus one as a sum of the integrands `u_k^x(t)`, up to the factor
`(4πt)^{-1/2}`. Integrating in time then exchanges sum and integral, using the summability of
`∫ |u_k^x|`.

Main results:
* `Riesz1.hasSum_gaussAverage`: `∑_k A_k(t) = √(4πt)`.
* `Riesz1.heat_sub_one_eq`: `W_t(x) - 1 = (4πt)^{-1/2} ∑_k (e^{-(x-k)²/(4t)} - A_k(t))`.
* `Riesz1.integral_heat_eq_interchange`: the time integral of `(W_t(x) - 1) t^{-(1+s)/2}` equals
  `(4π)^{-1/2} ∑_k ∫_{(0,∞)} u_k^x(t) dt`.
-/

public section

open MeasureTheory Set Filter Topology

namespace Riesz1

/-- The heat kernel series `∑_k e^{-4π²k²t} cos(2πkx)` is the circle heat kernel `W_t(x)`. -/
theorem circleHeatKernel_eq_series (t : ℝ) (ht : 0 < t) (x : ℝ) :
    circleHeatKernel t ht x =
      ∑' k : ℤ, Real.exp (-4 * Real.pi ^ 2 * (k : ℝ) ^ 2 * t) *
        Real.cos (2 * Real.pi * k * x) := by
  rw [circleHeatKernel_eq_re_tsum t ht x, Complex.re_tsum (summable_jacobiTheta₂_term_heat ht x)]
  exact tsum_congr fun n => re_jacobiTheta₂_term_heat t n x

/-- The periodized Gaussian is the heat kernel up to the factor `(4πt)^{1/2}`. -/
lemma tsum_gauss_eq_mul_heat {t : ℝ} (ht : 0 < t) (y : ℝ) :
    ∑' n : ℤ, Real.exp (-(y - n) ^ 2 / (4 * t)) =
      (4 * Real.pi * t) ^ (1 / 2 : ℝ) * circleHeatKernel t ht y := by
  rw [circleHeatKernel_eq_gauss t ht y, ← mul_assoc, ← Real.rpow_add (by positivity)]
  norm_num

/-- The averages of the Gaussians over `[0, 1]` sum to `√(4πt)`, the whole-line integral of the
Gaussian `exp(-y²/(4t))`. -/
theorem hasSum_gaussAverage {t : ℝ} (ht : 0 < t) :
    HasSum (fun k : ℤ => gaussAverage k t) (Real.sqrt (4 * Real.pi * t)) := by
  have hcont : Continuous fun y : ℝ => ∑' n : ℤ, Real.exp (-(y - n) ^ 2 / (4 * t)) := by
    have e : (fun y : ℝ => ∑' n : ℤ, Real.exp (-(y - n) ^ 2 / (4 * t))) =
        fun y : ℝ => (4 * Real.pi * t) ^ (1 / 2 : ℝ) * circleHeatKernel t ht y := by
      funext y
      exact tsum_gauss_eq_mul_heat ht y
    rw [e]
    exact (continuous_circleHeatKernel t ht).const_mul _
  have hDC := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := 0) (b := 1)
    (F := fun (k : ℤ) (y : ℝ) => Real.exp (-(y - k) ^ 2 / (4 * t)))
    (f := fun y : ℝ => ∑' k : ℤ, Real.exp (-(y - k) ^ 2 / (4 * t)))
    (fun (k : ℤ) (y : ℝ) => Real.exp (-(y - k) ^ 2 / (4 * t)))
    (fun k => (continuous_gauss_shift k t).aestronglyMeasurable)
    (fun k => Filter.Eventually.of_forall fun y _ => (Real.norm_of_nonneg (Real.exp_pos _).le).le)
    (Filter.Eventually.of_forall fun y _ => summable_gauss_int t ht y)
    (hcont.intervalIntegrable 0 1)
    (Filter.Eventually.of_forall fun y _ => (summable_gauss_int t ht y).hasSum)
  have hint : (∫ y in (0 : ℝ)..1, ∑' k : ℤ, Real.exp (-(y - k) ^ 2 / (4 * t))) =
      Real.sqrt (4 * Real.pi * t) := by
    simp_rw [tsum_gauss_eq_mul_heat ht]
    rw [intervalIntegral.integral_const_mul, intervalIntegral_circleHeatKernel, mul_one,
      Real.sqrt_eq_rpow]
  rw [hint] at hDC
  exact hDC

/-- The heat kernel minus one is `(4πt)^{-1/2}` times the sum of the Gaussian differences
`e^{-(x-k)²/(4t)} - A_k(t)`, for `t > 0`. -/
theorem heat_sub_one_eq {t : ℝ} (ht : 0 < t) (x : ℝ) :
    circleHeatKernel t ht x - 1 = (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) *
      ∑' k : ℤ, (Real.exp (-(x - k) ^ 2 / (4 * t)) - gaussAverage k t) := by
  have hA : Summable fun k : ℤ => gaussAverage k t := (hasSum_gaussAverage ht).summable
  have hE : Summable fun k : ℤ => Real.exp (-(x - k) ^ 2 / (4 * t)) := summable_gauss_int t ht x
  have hone : (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * ∑' k : ℤ, gaussAverage k t = 1 := by
    rw [(hasSum_gaussAverage ht).tsum_eq, Real.sqrt_eq_rpow, ← Real.rpow_add (by positivity)]
    norm_num
  rw [Summable.tsum_sub hE hA, circleHeatKernel_eq_gauss t ht x, mul_sub, hone]

/-- The integrand of the time integral, `(W_t(x) - 1) t^{-(1+s)/2}`, equals
`(4π)^{-1/2} ∑_k u_k^x(t)` for `t > 0`. -/
theorem integrand_eq_interchange {s x : ℝ} {t : ℝ} (ht : 0 < t) :
    (circleHeatKernel t ht x - 1) * t ^ (-(1 + s) / 2) =
      (4 * Real.pi) ^ (-(1 / 2 : ℝ)) * ∑' k : ℤ, interchangeTerm s x k t := by
  have hsplit : t ^ (-(1 / 2 : ℝ)) * t ^ (-(1 + s) / 2) = t ^ (-1 - s / 2) := by
    rw [← Real.rpow_add ht]
    congr 1
    ring
  have hmul : (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) =
      (4 * Real.pi) ^ (-(1 / 2 : ℝ)) * t ^ (-(1 / 2 : ℝ)) :=
    Real.mul_rpow (by positivity) ht.le
  have hint : ∑' k : ℤ, interchangeTerm s x k t =
      t ^ (-1 - s / 2) * ∑' k : ℤ, (Real.exp (-(x - k) ^ 2 / (4 * t)) - gaussAverage k t) := by
    rw [← tsum_mul_left]
    rfl
  rw [heat_sub_one_eq ht x, hint, hmul, ← hsplit]
  ring

/-- The time integral of `(W_t(x) - 1) t^{-(1+s)/2}` over `(0, ∞)` equals
`(4π)^{-1/2} ∑_k ∫_{(0,∞)} u_k^x(t) dt`, for `0 < s < 1` and `0 < x < 1`. Sum and integral are
exchanged by the summability of the absolute integrals. -/
theorem integral_heat_eq_interchange {s x : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hx0 : 0 < x)
    (hx1 : x < 1) :
    ∫ t in Ioi (0 : ℝ), (∑' k : ℤ, Real.exp (-4 * Real.pi ^ 2 * (k : ℝ) ^ 2 * t) *
        Real.cos (2 * Real.pi * k * x) - 1) * t ^ (-(1 + s) / 2) =
      (4 * Real.pi) ^ (-(1 / 2 : ℝ)) * ∑' k : ℤ, ∫ t in Ioi (0 : ℝ), interchangeTerm s x k t := by
  have hcongr : ∫ t in Ioi (0 : ℝ), (∑' k : ℤ, Real.exp (-4 * Real.pi ^ 2 * (k : ℝ) ^ 2 * t) *
        Real.cos (2 * Real.pi * k * x) - 1) * t ^ (-(1 + s) / 2) =
      ∫ t in Ioi (0 : ℝ), (4 * Real.pi) ^ (-(1 / 2 : ℝ)) *
        ∑' k : ℤ, interchangeTerm s x k t :=
    setIntegral_congr_fun measurableSet_Ioi (fun t ht => by
      have ht0 : (0 : ℝ) < t := ht
      rw [← circleHeatKernel_eq_series t ht0 x]
      exact integrand_eq_interchange (x := x) (s := s) ht0)
  rw [hcongr, integral_const_mul]
  congr 1
  exact (integral_tsum_of_summable_integral_norm (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun (k : ℤ) (t : ℝ) => interchangeTerm s x k t)
    (fun k => integrableOn_interchangeTerm hs0 hs1 hx0 hx1 k)
    (by simp only [Real.norm_eq_abs]; exact summable_integral_abs_interchangeTerm hs0 hs1 hx0 hx1)).symm

end Riesz1
