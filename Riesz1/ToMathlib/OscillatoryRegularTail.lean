/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.PuncturedOscillatoryIntegral

/-!
# Uniform oscillatory bounds for a regular tail

An integrable power bound on the derivative gives a reciprocal-frequency estimate
independent of the remote endpoint. This supports the tail step.
-/

public section

open MeasureTheory Set intervalIntegral

namespace Riesz1.PuncturedDerivative

/-- Integration by parts on a positive tail. The bound is independent of its far endpoint. -/
theorem norm_oscillatory_regular_tail_le {q : ℝ → ℝ} {R z M C e : ℝ}
    (hR : 0 < R) (hRz : R ≤ z) (hC : 0 ≤ C) (he : e < -1)
    (hq : ∀ t ∈ Icc R z, DifferentiableAt ℝ q t)
    (hM : ∀ t ∈ Icc R z, |q t| ≤ M)
    (hbound : ∀ t ∈ Icc R z, |deriv q t| ≤ C * t ^ e)
    {χ : ℝ → ℂ} {c : ℂ} (hc : c ≠ 0)
    (hχ : ∀ t : ℝ, HasDerivAt χ (c * χ t) t) (hn : ∀ t : ℝ, ‖χ t‖ = 1) :
    ‖∫ t in R..z, (q t : ℂ) * χ t‖ ≤
      (2 * M + C / (-e - 1) * R ^ (e + 1)) / ‖c‖ := by
  have hχc : Continuous χ := continuous_iff_continuousAt.mpr fun t => (hχ t).continuousAt
  have hqc : ContinuousOn q (uIcc R z) := by
    rw [uIcc_of_le hRz]
    exact fun t ht => (hq t ht).continuousAt.continuousWithinAt
  have hpow : IntervalIntegrable (fun t : ℝ => t ^ e) volume R z := by
    apply intervalIntegrable_rpow
    right
    rw [uIcc_of_le hRz]
    exact fun ht => not_lt_of_ge ht.1 hR
  have hd : IntervalIntegrable (deriv q) volume R z := by
    apply (hpow.const_mul C).mono_fun (measurable_deriv q).aestronglyMeasurable.restrict
    rw [uIoc_of_le hRz]
    exact ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => by
      dsimp only
      rw [Real.norm_eq_abs, Real.norm_of_nonneg (mul_nonneg hC (Real.rpow_nonneg (hR.le.trans ht.1.le) e))]
      exact hbound t ⟨ht.1.le, ht.2⟩
  have hdC : IntervalIntegrable (fun t : ℝ => ((deriv q t : ℝ) : ℂ)) volume R z :=
    ⟨Complex.ofRealCLM.integrable_comp hd.1, Complex.ofRealCLM.integrable_comp hd.2⟩
  have hparts := integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (Complex.continuous_ofReal.comp_continuousOn hqc) hχc.continuousOn
    (fun t ht => (hq t ⟨by rw [min_eq_left hRz] at ht; exact ht.1.le,
      by rw [max_eq_right hRz] at ht; exact ht.2.le⟩).hasDerivAt.ofReal_comp)
    (fun t _ => hχ t) hdC ((continuous_const.mul hχc).intervalIntegrable R z)
  have hparts' : c * (∫ t in R..z, (q t : ℂ) * χ t) =
      (q z : ℂ) * χ z - (q R : ℂ) * χ R -
        ∫ t in R..z, ((deriv q t : ℝ) : ℂ) * χ t := by
    simp only [Function.comp_apply] at hparts
    rw [← intervalIntegral.integral_const_mul]
    convert hparts using 1
    congr 1
    funext t
    ring
  have hdb := intervalIntegral.norm_integral_le_of_norm_le
    (f := fun t : ℝ => ((deriv q t : ℝ) : ℂ) * χ t) hRz
    (ae_of_all volume fun t (ht : t ∈ Ioc R z) => by
      rw [norm_mul, hn, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact hbound t ⟨ht.1.le, ht.2⟩) (hpow.const_mul C)
  have hval : (∫ t in R..z, C * t ^ e) = C / (-e - 1) * (R ^ (e + 1) - z ^ (e + 1)) := by
    rw [intervalIntegral.integral_const_mul, integral_rpow]
    · rw [show -e - 1 = -(e + 1) by ring, div_neg]
      ring
    · right
      refine ⟨by linarith, ?_⟩
      rw [uIcc_of_le hRz]
      exact fun ht => not_lt_of_ge ht.1 hR
  rw [hval] at hdb
  have hdb' : ‖∫ t in R..z, ((deriv q t : ℝ) : ℂ) * χ t‖ ≤
      C / (-e - 1) * R ^ (e + 1) := by
    have hp : 0 ≤ C / (-e - 1) * z ^ (e + 1) :=
      mul_nonneg (div_nonneg hC (by linarith)) (Real.rpow_nonneg (hR.le.trans hRz) _)
    linarith
  have hh := norm_sub_le ((q z : ℂ) * χ z - (q R : ℂ) * χ R)
    (∫ t in R..z, ((deriv q t : ℝ) : ℂ) * χ t)
  have hh' := norm_sub_le ((q z : ℂ) * χ z) ((q R : ℂ) * χ R)
  rw [← hparts', norm_mul] at hh
  simp only [norm_mul, hn, mul_one, Complex.norm_real, Real.norm_eq_abs] at hh'
  apply (le_div_iff₀ (norm_pos_iff.mpr hc)).mpr
  nlinarith [hh, hh', hdb', hM R (left_mem_Icc.mpr hRz), hM z (right_mem_Icc.mpr hRz)]

end Riesz1.PuncturedDerivative
