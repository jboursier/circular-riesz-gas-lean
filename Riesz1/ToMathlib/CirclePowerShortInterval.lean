/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.CircleWindowPowerIntegrable
public import Riesz1.ToMathlib.FiniteMarkMollify
public import Riesz1.ToMathlib.PeriodicConvolutionSmoothing

/-!
# Circle power integrals over short intervals

An interval of length `d ≤ L` has singular power mass `O(d^(1-γ))`,
uniformly in its position and the position of the singularity. Split at
circular distance `d`, and bound the near part by a whole-period mass.
-/

public section

open MeasureTheory Set Filter

namespace Riesz1

/-- The mass of an integrable circle singularity on a short real interval. -/
theorem integral_circle_power_short_interval_le {L γ x y : ℝ}
    (hL : 0 < L) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hxy : x < y) (hshort : y - x ≤ L) (a : ℝ) :
    (∫ t in x..y, circDist L (t - a) ^ (-γ)) ≤
      (1 + 2 / (1 - γ)) * (y - x) ^ (1 - γ) := by
  let d := y - x
  have hd : 0 < d := sub_pos.mpr hxy
  let V := fun t => circDist L (t - a) ^ (-γ)
  let U := fun t => (Iic d).indicator (fun u : ℝ => u ^ (-γ)) (circDist L (t - a))
  have hUp : Function.Periodic U L := fun t => by
    dsimp only [U]
    rw [show t + L - a = (t - a) + L by ring, circDist_add_period hL]
  have hUi : IntegrableOn U (Ioc (-(L / 2)) (L / 2)) :=
    integrableOn_window_circDist_comp_sub hL _ a
      (intervalIntegrable_abs_rpow_indicator_Iic (by linarith : -1 < -γ) (by positivity))
  have hUxy : IntervalIntegrable U volume x y :=
    PeriodicConvolution.intervalIntegrable_of_period hL hUp hUi x y
  have hUxL : IntervalIntegrable U volume x (x + L) :=
    PeriodicConvolution.intervalIntegrable_of_period hL hUp hUi x (x + L)
  have hVi : IntervalIntegrable V volume x y := by
    have hi := locallyIntegrable_translate_sub
      (locallyIntegrable_circle_dist_rpow hL (by linarith : -1 < -γ)) a
    simpa only [V, dist_coe_zero_eq_circDist] using
      (hi.integrableOn_isCompact isCompact_uIcc).intervalIntegrable (a := x) (b := y)
  have hmass : (∫ t in x..y, U t) ≤ 2 * d ^ (1 - γ) / (1 - γ) := by
    have hsub : Ioc x y ⊆ Ioc x (x + L) := Ioc_subset_Ioc le_rfl (by linarith)
    calc (∫ t in x..y, U t) ≤ ∫ t in x..(x + L), U t := by
          rw [intervalIntegral.integral_of_le hxy.le,
            intervalIntegral.integral_of_le (by linarith : x ≤ x + L)]
          exact setIntegral_mono_set
            ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp hUxL)
            (ae_of_all _ fun t => indicator_nonneg (fun u hu =>
              Real.rpow_nonneg (circDist_nonneg L (t - a)) _) _) (ae_of_all _ hsub)
      _ = ∫ t in Ioc (-(L / 2)) (L / 2), U t := by
          rw [← intervalIntegral.integral_of_le (by linarith : -(L / 2) ≤ L / 2)]
          convert hUp.intervalIntegral_add_eq x (-(L / 2)) using 1; congr 1; ring
      _ ≤ _ := by
          simpa only [U, show -γ + 1 = 1 - γ by ring] using
            setIntegral_window_circDist_rpow_Iic_le hL (by linarith : -1 < -γ) hd a
  calc (∫ t in x..y, V t) ≤ ∫ t in x..y, U t + d ^ (-γ) := by
        apply intervalIntegral.integral_mono_ae_restrict hxy.le hVi (hUxy.add intervalIntegrable_const)
        exact ae_of_all _ fun t => by
          dsimp only [V, U]
          by_cases ht : circDist L (t - a) ≤ d
          · rw [indicator_of_mem (show circDist L (t - a) ∈ Iic d from ht)]
            exact le_add_of_nonneg_right (Real.rpow_nonneg hd.le _)
          · rw [indicator_of_notMem (show circDist L (t - a) ∉ Iic d from ht), zero_add]
            exact Real.rpow_le_rpow_of_nonpos hd (le_of_lt (lt_of_not_ge ht)) (by linarith)
    _ = (∫ t in x..y, U t) + d * d ^ (-γ) := by
        rw [intervalIntegral.integral_add hUxy intervalIntegrable_const,
          intervalIntegral.integral_const, smul_eq_mul]
    _ ≤ 2 * d ^ (1 - γ) / (1 - γ) + d * d ^ (-γ) := add_le_add hmass le_rfl
    _ = (1 + 2 / (1 - γ)) * d ^ (1 - γ) := by
        have he : d * d ^ (-γ) = d ^ (1 - γ) := by
          conv_lhs => lhs; rw [← Real.rpow_one d]
          rw [← Real.rpow_add hd]
          congr 1
        rw [he]
        ring

end Riesz1
