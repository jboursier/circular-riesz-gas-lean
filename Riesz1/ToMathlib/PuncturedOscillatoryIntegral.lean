/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.PuncturedDerivative
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Oscillatory integrals with a power singularity at an endpoint

The cutoff argument on one half-interval: integrate the near
part absolutely and the complement by parts. The oscillating factor is specified by its
unit norm and constant logarithmic derivative, so the result applies to every Fourier
character and every circle length with the same constants.
-/

public section

open MeasureTheory Set intervalIntegral

namespace Riesz1.PuncturedDerivative

/-- The cutoff estimate for an oscillatory integral on a half-interval with one singular
endpoint. The constant involves only the endpoint value and the derivative bound. -/
theorem norm_oscillatory_integral_le_cutoff {q : ℝ → ℝ} {b C R h : ℝ}
    (hb : 0 < b) (hb1 : b < 1) (hC : 0 ≤ C) (hR : 0 < R)
    (hq : ∀ x ∈ Ioc 0 R, DifferentiableAt ℝ q x)
    (hbound : ∀ x ∈ Ioc 0 R, |deriv q x| ≤ C * x ^ (-1 - b))
    {χ : ℝ → ℂ} {c : ℂ} (hc : c ≠ 0)
    (hχ : ∀ t : ℝ, HasDerivAt χ (c * χ t) t) (hχnorm : ∀ t : ℝ, ‖χ t‖ = 1)
    (hh : 0 < h) (hhR : h ≤ R) :
    ‖∫ t in (0 : ℝ)..R, (q t : ℂ) * χ t‖ ≤
      |q R| * h + (C / b / (1 - b)) * h ^ (1 - b) +
        (2 * |q R| + 2 * (C / b) * h ^ (-b)) / ‖c‖ := by
  have hχcont : Continuous χ := continuous_iff_continuousAt.mpr fun t => (hχ t).continuousAt
  have hqint : IntervalIntegrable q volume 0 R := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le]
    exact integrableOn_of_deriv_rpow_bound hb hb1 hC hR hq hbound
  have hqCint : IntervalIntegrable (fun t : ℝ => (q t : ℂ)) volume 0 R :=
    ⟨Complex.ofRealCLM.integrable_comp hqint.1, Complex.ofRealCLM.integrable_comp hqint.2⟩
  have hprod := hqCint.mul_continuousOn hχcont.continuousOn
  have hnearInt : IntervalIntegrable (fun t : ℝ => (q t : ℂ) * χ t) volume 0 h :=
    hprod.mono_set (by rw [uIcc_of_le hh.le, uIcc_of_le hR.le]; exact Icc_subset_Icc le_rfl hhR)
  have hfarInt : IntervalIntegrable (fun t : ℝ => (q t : ℂ) * χ t) volume h R :=
    hprod.mono_set (by rw [uIcc_of_le hhR, uIcc_of_le hR.le]; exact Icc_subset_Icc hh.le le_rfl)
  have hpowNear : IntervalIntegrable (fun t : ℝ => |q R| + C / b * t ^ (-b)) volume 0 h :=
    (intervalIntegrable_const).add ((intervalIntegrable_rpow' (by linarith : -1 < -b)).const_mul _)
  have hnear := intervalIntegral.norm_integral_le_of_norm_le (f := fun t : ℝ => (q t : ℂ) * χ t) hh.le
    (ae_of_all volume fun t (ht : t ∈ Ioc 0 h) => by
      rw [norm_mul, hχnorm, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact abs_le_rpow_of_deriv_bound hb hC hR hq hbound ⟨ht.1, ht.2.trans hhR⟩)
    hpowNear
  have hnearValue : (∫ t in (0 : ℝ)..h, |q R| + C / b * t ^ (-b)) =
      |q R| * h + (C / b / (1 - b)) * h ^ (1 - b) := by
    rw [integral_add intervalIntegrable_const ((intervalIntegrable_rpow' (by linarith : -1 < -b)).const_mul _),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith : -1 < -b))]
    rw [show -b + 1 = 1 - b by ring, Real.zero_rpow (by linarith : 1 - b ≠ 0)]
    simp only [sub_zero, smul_eq_mul]
    ring
  rw [hnearValue] at hnear
  have hqcont : ContinuousOn q (uIcc h R) := by
    rw [uIcc_of_le hhR]
    exact fun t ht => (hq t ⟨hh.trans_le ht.1, ht.2⟩).continuousAt.continuousWithinAt
  have hpow : IntervalIntegrable (fun t : ℝ => t ^ (-1 - b)) volume h R := by
    apply intervalIntegrable_rpow
    right
    rw [uIcc_of_le hhR]
    exact fun ht => not_lt_of_ge ht.1 hh
  have hderivInt : IntervalIntegrable (deriv q) volume h R := by
    apply (hpow.const_mul C).mono_fun (measurable_deriv q).aestronglyMeasurable.restrict
    rw [uIoc_of_le hhR]
    exact ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => by
      dsimp only
      rw [Real.norm_eq_abs, Real.norm_of_nonneg (mul_nonneg hC (Real.rpow_nonneg (le_of_lt (hh.trans ht.1)) _))]
      exact hbound t ⟨hh.trans ht.1, ht.2⟩
  have hderivCInt : IntervalIntegrable (fun t : ℝ => ((deriv q t : ℝ) : ℂ)) volume h R :=
    ⟨Complex.ofRealCLM.integrable_comp hderivInt.1, Complex.ofRealCLM.integrable_comp hderivInt.2⟩
  have hχderivInt : IntervalIntegrable (fun t : ℝ => c * χ t) volume h R :=
    (continuous_const.mul hχcont).intervalIntegrable h R
  have hparts := integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (Complex.continuous_ofReal.comp_continuousOn hqcont) hχcont.continuousOn
    (fun t ht => (hq t ⟨by rw [min_eq_left hhR] at ht; linarith [ht.1],
      by rw [max_eq_right hhR] at ht; exact ht.2.le⟩).hasDerivAt.ofReal_comp)
    (fun t _ => hχ t) hderivCInt hχderivInt
  have hparts' : c * (∫ t in h..R, (q t : ℂ) * χ t) =
      (q R : ℂ) * χ R - (q h : ℂ) * χ h -
        ∫ t in h..R, ((deriv q t : ℝ) : ℂ) * χ t := by
    simp only [Function.comp_apply] at hparts
    rw [← intervalIntegral.integral_const_mul]
    convert hparts using 1
    congr 1
    funext t
    ring
  have hderivBound := intervalIntegral.norm_integral_le_of_norm_le (f := fun t : ℝ => ((deriv q t : ℝ) : ℂ) * χ t) hhR
    (ae_of_all volume fun t (ht : t ∈ Ioc h R) => by
      rw [norm_mul, hχnorm, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact hbound t ⟨hh.trans ht.1, ht.2⟩) (hpow.const_mul C)
  have hpowValue : (∫ t in h..R, C * t ^ (-1 - b)) =
      C / b * (h ^ (-b) - R ^ (-b)) := by
    rw [intervalIntegral.integral_const_mul, integral_rpow]
    · rw [show -1 - b + 1 = -b by ring]
      field_simp
      ring
    · right
      refine ⟨by linarith, ?_⟩
      rw [uIcc_of_le hhR]
      exact fun ht => not_lt_of_ge ht.1 hh
  rw [hpowValue] at hderivBound
  have hderivLe : ‖∫ t in h..R, ((deriv q t : ℝ) : ℂ) * χ t‖ ≤ C / b * h ^ (-b) := by
    have : 0 ≤ C / b * R ^ (-b) := by positivity
    linarith
  have hend := abs_le_rpow_of_deriv_bound hb hC hR hq hbound ⟨hh, hhR⟩
  have hnorm := norm_sub_le ((q R : ℂ) * χ R - (q h : ℂ) * χ h)
    (∫ t in h..R, ((deriv q t : ℝ) : ℂ) * χ t)
  have hnorm' := norm_sub_le ((q R : ℂ) * χ R) ((q h : ℂ) * χ h)
  rw [← hparts', norm_mul] at hnorm
  simp only [norm_mul, hχnorm, mul_one, Complex.norm_real, Real.norm_eq_abs] at hnorm'
  have hfar : ‖∫ t in h..R, (q t : ℂ) * χ t‖ ≤
      (2 * |q R| + 2 * (C / b) * h ^ (-b)) / ‖c‖ := by
    apply (le_div_iff₀ (norm_pos_iff.mpr hc)).mpr
    nlinarith [hnorm, hnorm', hderivLe, hend]
  rw [← integral_add_adjacent_intervals hnearInt hfarInt]
  exact (norm_add_le _ _).trans (add_le_add hnear hfar)

/-- Choosing the reciprocal-frequency cutoff gives decay of order `‖c‖^(b-1)`.
The same explicit constant works for every unit-modulus oscillation with derivative `c χ`.
The frequency threshold ensures that the cutoff lies within the half-interval. -/
theorem norm_oscillatory_integral_le_rpow {q : ℝ → ℝ} {b C R : ℝ}
    (hb : 0 < b) (hb1 : b < 1) (hC : 0 ≤ C) (hR : 0 < R)
    (hq : ∀ x ∈ Ioc 0 R, DifferentiableAt ℝ q x)
    (hbound : ∀ x ∈ Ioc 0 R, |deriv q x| ≤ C * x ^ (-1 - b))
    {χ : ℝ → ℂ} {c : ℂ} (hfreq : 1 ≤ ‖c‖) (hfreqR : ‖c‖⁻¹ ≤ R)
    (hχ : ∀ t : ℝ, HasDerivAt χ (c * χ t) t) (hχnorm : ∀ t : ℝ, ‖χ t‖ = 1) :
    ‖∫ t in (0 : ℝ)..R, (q t : ℂ) * χ t‖ ≤
      (3 * |q R| + C / b / (1 - b) + 2 * (C / b)) * ‖c‖ ^ (b - 1) := by
  have hcpos : 0 < ‖c‖ := lt_of_lt_of_le zero_lt_one hfreq
  have hc : c ≠ 0 := norm_pos_iff.mp hcpos
  let h : ℝ := ‖c‖⁻¹
  have hh : 0 < h := inv_pos.mpr hcpos
  have hh1 : h ≤ 1 := (inv_le_one₀ hcpos).mpr hfreq
  have hcut := norm_oscillatory_integral_le_cutoff hb hb1 hC hR hq hbound hc
    hχ hχnorm hh hfreqR
  have hpow : h * h ^ (-b) = h ^ (1 - b) := by
    simpa only [Real.rpow_one, sub_eq_add_neg] using (Real.rpow_add hh 1 (-b)).symm
  have hhpow : h ≤ h ^ (1 - b) := by
    conv_lhs => rw [← Real.rpow_one h]
    exact Real.rpow_le_rpow_of_exponent_ge hh hh1 (by linarith)
  have hscale : h ^ (1 - b) = ‖c‖ ^ (b - 1) := by
    dsimp [h]
    rw [Real.inv_rpow hcpos.le, ← Real.rpow_neg hcpos.le]
    congr 1
    ring
  have hfar : (2 * |q R| + 2 * (C / b) * h ^ (-b)) / ‖c‖ =
      2 * |q R| * h + 2 * (C / b) * h ^ (1 - b) := by
    rw [div_eq_mul_inv]
    change (2 * |q R| + 2 * (C / b) * h ^ (-b)) * h = _
    rw [show (2 * |q R| + 2 * (C / b) * h ^ (-b)) * h =
      2 * |q R| * h + 2 * (C / b) * (h * h ^ (-b)) by ring, hpow]
  change ‖∫ t in (0 : ℝ)..R, (q t : ℂ) * χ t‖ ≤
    |q R| * h + (C / b / (1 - b)) * h ^ (1 - b) +
      (2 * |q R| + 2 * (C / b) * h ^ (-b)) / ‖c‖ at hcut
  rw [hfar] at hcut
  rw [← hscale]
  nlinarith [mul_le_mul_of_nonneg_left hhpow (abs_nonneg (q R))]

end Riesz1.PuncturedDerivative
