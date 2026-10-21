/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingZArc
public import Riesz1.ToMathlib.CircleWindowPowerIntegrable

/-!
# Integrated capped power envelopes

The near-mark energy calculation in Proposition 5.6.
A positive power loss treats the logarithmic endpoint with the same
formula as both noncritical regimes. Constants precede the cutoff scale.
-/

public section

open MeasureTheory Set

namespace Riesz1

/-- Integration of the squared near-mark envelope, including `2b = 1`.
The estimate is uniform for every `K ≥ 1`, including `K = 1`. -/
theorem integral_capped_power_square_le (b δ : ℝ) (hδ : 0 < δ)
    {K : ℝ} (hK : 1 ≤ K) :
    ∫ t in (0 : ℝ)..1, max t K⁻¹ ^ (-2 * b) ≤
      (1 + 1 / δ) * K ^ δ * (1 + K ^ (2 * b - 1)) := by
  have hK0 : 0 < K := by linarith
  have hh : 0 < K⁻¹ := inv_pos.mpr hK0
  have hh1 : K⁻¹ ≤ 1 := (inv_le_one₀ hK0).mpr hK
  let e := max (2 * b - 1) 0 + δ
  have he : 0 ≤ e := by dsimp [e]; linarith [le_max_right (2 * b - 1) 0]
  have hc (a : ℝ) : Continuous (fun t : ℝ => max t K⁻¹ ^ a) :=
    Continuous.rpow_const (continuous_id.max continuous_const)
      (fun t => Or.inl (ne_of_gt (hh.trans_le (le_max_right _ _))))
  have hpt (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      max t K⁻¹ ^ (-2 * b) ≤ K ^ e * max t K⁻¹ ^ (-(1 - δ)) := by
    have hx : 0 < max t K⁻¹ := hh.trans_le (le_max_right _ _)
    have hx1 : max t K⁻¹ ≤ 1 := max_le ht.2 hh1
    have hsplit : max t K⁻¹ ^ (-2 * b) =
        max t K⁻¹ ^ (-e) * max t K⁻¹ ^ (e - 2 * b) := by
      rw [← Real.rpow_add hx]
      congr 1
      ring
    have hfirst : max t K⁻¹ ^ (-e) ≤ K ^ e := by
      calc _ ≤ (K⁻¹) ^ (-e) := Real.rpow_le_rpow_of_nonpos hh (le_max_right _ _) (by linarith)
           _ = _ := by rw [Real.inv_rpow hK0.le, Real.rpow_neg hK0.le, inv_inv]
    have hsecond : max t K⁻¹ ^ (e - 2 * b) ≤ max t K⁻¹ ^ (-(1 - δ)) :=
      Real.rpow_le_rpow_of_exponent_ge hx hx1 (by dsimp [e]; linarith [le_max_left (2 * b - 1) 0])
    rw [hsplit]
    exact mul_le_mul hfirst hsecond (by positivity) (by positivity)
  have hi := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    ((hc (-2 * b)).intervalIntegrable (μ := volume) _ _)
    (((hc (-(1 - δ))).const_mul (K ^ e)).intervalIntegrable (μ := volume) _ _) hpt
  rw [intervalIntegral.integral_const_mul] at hi
  have hb := integral_max_rpow_le (a := 1 - δ) (c := K⁻¹) (T := 1)
    (by linarith) hh (by norm_num)
  rw [show 1 - (1 - δ) = δ by ring, max_eq_left hh1, Real.one_rpow, mul_one, mul_one] at hb
  have hp : K ^ e ≤ K ^ δ * (1 + K ^ (2 * b - 1)) := by
    rw [show e = δ + max (2 * b - 1) 0 by dsimp [e]; ring, Real.rpow_add hK0]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rcases le_total (2 * b - 1) 0 with h | h
    · rw [max_eq_right h, Real.rpow_zero]
      linarith [Real.rpow_nonneg hK0.le (2 * b - 1)]
    · rw [max_eq_left h]
      linarith
  calc _ ≤ K ^ e * (1 + 1 / δ) := hi.trans (mul_le_mul_of_nonneg_left hb (by positivity))
       _ ≤ (K ^ δ * (1 + K ^ (2 * b - 1))) * (1 + 1 / δ) :=
         mul_le_mul_of_nonneg_right hp (by positivity)
       _ = _ := by ring

/-- Integrability of the capped power on every centered real interval,
after restricting it to the unit neighborhood. -/
theorem intervalIntegrable_abs_capped_power_indicator {h : ℝ} (hh : 0 < h)
    (e a : ℝ) :
    IntervalIntegrable (fun y : ℝ =>
      (Iic (1 : ℝ)).indicator (fun t => max t h ^ e) |y|) volume (-a) a := by
  have hc : Continuous (fun t : ℝ => max t h ^ e) :=
    Continuous.rpow_const (continuous_id.max continuous_const)
      (fun t => Or.inl (ne_of_gt (hh.trans_le (le_max_right _ _))))
  apply ((hc.comp continuous_abs).intervalIntegrable (μ := volume) (-a) a).mono_fun'
    ((hc.measurable.indicator measurableSet_Iic).comp continuous_abs.measurable).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun y => by
    simp only [Function.comp_apply, Real.norm_eq_abs]
    by_cases hy : |y| ≤ 1
    · rw [indicator_of_mem (show |y| ∈ Iic (1 : ℝ) from hy), abs_of_nonneg (by positivity)]
    · rw [indicator_of_notMem (show |y| ∉ Iic (1 : ℝ) from hy), abs_zero]
      positivity

/-- The capped near-mark square has bounded mass on every circle,
uniformly in the circumference and the center. -/
theorem setIntegral_window_capped_power_square_le {L K b δ : ℝ}
    (hL : 0 < L) (hK : 1 ≤ K) (hδ : 0 < δ) (c : ℝ) :
    ∫ y in Ioc (-(L / 2)) (L / 2),
      (Iic (1 : ℝ)).indicator (fun t => max t K⁻¹ ^ (-2 * b)) (circDist L (y - c)) ≤
        2 * (1 + 1 / δ) * K ^ δ * (1 + K ^ (2 * b - 1)) := by
  have hK0 : 0 < K := by linarith
  have hh : 0 < K⁻¹ := inv_pos.mpr hK0
  have hc : Continuous (fun t : ℝ => max t K⁻¹ ^ (-2 * b)) :=
    Continuous.rpow_const (continuous_id.max continuous_const)
      (fun t => Or.inl (ne_of_gt (hh.trans_le (le_max_right _ _))))
  let G := (Iic (1 : ℝ)).indicator (fun t => max t K⁻¹ ^ (-2 * b))
  have hi : IntervalIntegrable (fun y : ℝ => G |y|) volume (-(L / 2)) (L / 2) :=
    intervalIntegrable_abs_capped_power_indicator hh (-2 * b) (L / 2)
  rw [setIntegral_window_circDist_comp_sub hL G c hi]
  have hp : ∫ u in Ioc 0 (L / 2), G u ≤ ∫ u in Ioc (0 : ℝ) 1, max u K⁻¹ ^ (-2 * b) := by
    dsimp [G]
    rw [setIntegral_indicator measurableSet_Iic]
    apply setIntegral_mono_set
      ((hc.intervalIntegrable (μ := volume) 0 1).1)
      (Filter.Eventually.of_forall fun u => by positivity)
    exact Filter.Eventually.of_forall fun u hu => ⟨hu.1.1, hu.2⟩
  have he := integral_capped_power_square_le b δ hδ hK
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at he
  calc _ ≤ 2 * ∫ u in Ioc (0 : ℝ) 1, max u K⁻¹ ^ (-2 * b) :=
         mul_le_mul_of_nonneg_left hp (by norm_num)
       _ ≤ 2 * ((1 + 1 / δ) * K ^ δ * (1 + K ^ (2 * b - 1))) :=
         mul_le_mul_of_nonneg_left he (by norm_num)
       _ = _ := by ring

end Riesz1
