/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.CircleWindowPower

/-!
# Integrability certificates for truncated circle powers

These certificates discharge the integrability premise of the circle-window
reduction. The resulting bounds hold on every positive-length circle with
constants independent of the length and the center, for use in
Lemma 5.3.
-/

public section

open MeasureTheory Set Filter

namespace Riesz1

/-- Integrability in the central real window transfers to every center of
the circular window. This supplies absolute-integrability certificates in
addition to the numerical window-integral formulas. -/
theorem integrableOn_window_circDist_comp_sub {L : ℝ} (hL : 0 < L)
    (G : ℝ → ℝ) (c : ℝ)
    (hG : IntervalIntegrable (fun y => G |y|) volume (-(L / 2)) (L / 2)) :
    IntegrableOn (fun y => G (circDist L (y - c))) (Ioc (-(L / 2)) (L / 2)) := by
  have hbase : IntervalIntegrable (fun y => G (circDist L y))
      volume (-(L / 2)) (L / 2) := by
    apply hG.congr
    intro y hy
    rw [uIoc_of_le (by linarith)] at hy
    change G |y| = G (circDist L y)
    rw [circDist_eq_abs_of_mem_Icc hL ⟨hy.1.le, hy.2⟩]
  have hper : Function.Periodic (fun y => G (circDist L y)) L :=
    fun y => congrArg G (circDist_add_period hL y)
  have hbase' : IntervalIntegrable (fun y => G (circDist L y))
      volume (-(L / 2)) (-(L / 2) + L) := by
    simpa only [show -(L / 2) + L = L / 2 by ring] using hbase
  have hshift := (hper.intervalIntegrable hL.ne' hbase'
    (-(L / 2) - c) (L / 2 - c)).comp_sub_right c
  simp only [sub_add_cancel] at hshift
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp hshift

/-- An integrable power remains interval integrable after restricting to a
centered interval of any radius. -/
theorem intervalIntegrable_abs_rpow_indicator_Iic {e R A : ℝ}
    (he : -1 < e) (hA : 0 ≤ A) :
    IntervalIntegrable (fun y : ℝ => (Iic R).indicator (fun u => u ^ e) |y|)
      volume (-A) A := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)]
  have hm : Measurable (fun y : ℝ => (Iic R).indicator (fun u : ℝ => u ^ e) |y|) :=
    ((measurable_id.pow_const e).indicator measurableSet_Iic).comp continuous_abs.measurable
  refine (integrableOn_abs_rpow he hA).mono' hm.aestronglyMeasurable ?_
  exact Eventually.of_forall fun y => by
    by_cases hy : |y| ≤ R
    · rw [indicator_of_mem (show |y| ∈ Iic R from hy)]
      simp only [Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (abs_nonneg y) e)]
      exact le_rfl
    · rw [indicator_of_notMem (show |y| ∉ Iic R from hy), norm_zero]
      positivity

/-- A nonpositive power truncated away from zero is integrable on every
bounded symmetric interval, even when the untruncated power is not. -/
theorem intervalIntegrable_abs_rpow_indicator_Ici {e ρ A : ℝ}
    (he : e ≤ 0) (hρ : 0 < ρ) (hA : 0 ≤ A) :
    IntervalIntegrable (fun y : ℝ => (Ici ρ).indicator (fun u => u ^ e) |y|)
      volume (-A) A := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)]
  have hm : Measurable (fun y : ℝ => (Ici ρ).indicator (fun u : ℝ => u ^ e) |y|) :=
    ((measurable_id.pow_const e).indicator measurableSet_Ici).comp continuous_abs.measurable
  refine (integrableOn_const (C := ρ ^ e) (s := Icc (-A) A)
    (hs := measure_Icc_lt_top.ne)).mono'
    hm.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  by_cases hy : ρ ≤ |y|
  · rw [indicator_of_mem (show |y| ∈ Ici ρ from hy)]
    simp only [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg y) e)]
    exact Real.rpow_le_rpow_of_nonpos hρ hy he
  · rw [indicator_of_notMem (show |y| ∉ Ici ρ from hy), norm_zero]
    positivity

/-- Uniform local-mass bound for a circle power singularity truncated at `R`.
The exponent need only be greater than `-1`. -/
theorem setIntegral_window_circDist_rpow_Iic_le {L e R : ℝ}
    (hL : 0 < L) (he : -1 < e) (hR : 0 < R) (c : ℝ) :
    ∫ y in Ioc (-(L / 2)) (L / 2),
      (Iic R).indicator (fun u => u ^ e) (circDist L (y - c)) ≤
        2 * R ^ (e + 1) / (e + 1) := by
  rw [setIntegral_window_circDist_comp_sub hL _ c
    (intervalIntegrable_abs_rpow_indicator_Iic he (by positivity))]
  have h := setIntegral_Ioc_indicator_Iic_rpow_le (a := L / 2) he hR
  calc 2 * ∫ u in Ioc 0 (L / 2), (Iic R).indicator (fun u => u ^ e) u
      ≤ 2 * (R ^ (e + 1) / (e + 1)) := mul_le_mul_of_nonneg_left h (by norm_num)
    _ = _ := by ring

/-- Uniform tail bound for a nonintegrable power truncated away from zero. -/
theorem setIntegral_window_circDist_rpow_Ici_le {L e ρ : ℝ}
    (hL : 0 < L) (he : e < -1) (hρ : 0 < ρ) (c : ℝ) :
    ∫ y in Ioc (-(L / 2)) (L / 2),
      (Ici ρ).indicator (fun u => u ^ e) (circDist L (y - c)) ≤
        2 * (-ρ ^ (e + 1) / (e + 1)) := by
  rw [setIntegral_window_circDist_comp_sub hL _ c
    (intervalIntegrable_abs_rpow_indicator_Ici (by linarith) hρ (by positivity))]
  exact mul_le_mul_of_nonneg_left
    (setIntegral_Ioc_indicator_Ici_rpow_le (a := L / 2) he hρ) (by norm_num)

end Riesz1
