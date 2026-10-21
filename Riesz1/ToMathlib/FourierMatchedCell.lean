/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Tactic

/-!
# Fourier decay for cells with matching first derivatives

Three integrations by parts give cubic decay for a smooth unit cell whose values
and first derivatives match. The second derivatives may jump at the seam.
-/

public section

open MeasureTheory Set

namespace Riesz1

/-- The Fourier coefficients of a continuously differentiable unit cell have inverse
frequency decay, even when its endpoint values do not agree. -/
theorem exists_fourierCoeffOn_unit_bound {f : ℝ → ℂ} {a : ℝ}
    (hf : ∀ x ∈ Icc a (a + 1), ContDiffAt ℝ 1 f x) :
    ∃ K : ℝ, 0 < K ∧ ∀ k : ℤ, k ≠ 0 →
      ‖fourierCoeffOn (show a < a + 1 by linarith) f k‖ ≤
        K * |(k : ℝ)| ^ (-1 : ℝ) := by
  have hdc : ContinuousOn (deriv f) (Icc a (a + 1)) :=
    fun x hx => ((hf x hx).derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hdc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM a ⟨le_rfl, by linarith⟩)
  have hdi : IntervalIntegrable (deriv f) volume a (a + 1) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
    exact hdc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  refine ⟨(‖f (a + 1) - f a‖ + M + 1) / (2 * Real.pi), by positivity, fun k hk => ?_⟩
  have hF := fourierCoeffOn_of_hasDerivAt (by linarith : a < a + 1) hk
    (fun x hx => (hf x (by simpa only [uIcc_of_le (by linarith : a ≤ a + 1)] using hx)).differentiableAt
      (by norm_num) |>.hasDerivAt) hdi
  have hn : ‖fourierCoeffOn (show a < a + 1 by linarith) (deriv f) k‖ ≤ M := by
    rw [fourierCoeffOn_eq_integral]
    simp only [show a + 1 - a = 1 by ring, one_div_one, one_smul, smul_eq_mul]
    calc ‖∫ x in a..a + 1, fourier (-k) (x : AddCircle (a + 1 - a)) * deriv f x‖
        ≤ M * |a + 1 - a| := by
          apply intervalIntegral.norm_integral_le_of_norm_le_const
          intro x hx
          rw [norm_mul, fourier_apply, Circle.norm_coe, one_mul]
          exact hM x (by
            rw [uIoc_of_le (by linarith : a ≤ a + 1)] at hx
            exact ⟨hx.1.le, hx.2⟩)
      _ = M := by simp
  norm_num only [Complex.ofReal_add, Complex.ofReal_one, add_sub_cancel_left] at hF
  rw [hF, norm_mul]
  have hbr : ‖fourier (-k) (a : AddCircle (a + 1 - a)) * (f (a + 1) - f a) -
      (1 : ℂ) * fourierCoeffOn (by linarith : a < a + 1) (deriv f) k‖ ≤
      ‖f (a + 1) - f a‖ + M + 1 := by
    calc _ ≤ ‖fourier (-k) (a : AddCircle (a + 1 - a)) * (f (a + 1) - f a)‖ +
        ‖(1 : ℂ) * fourierCoeffOn (by linarith : a < a + 1) (deriv f) k‖ := norm_sub_le _ _
      _ ≤ ‖f (a + 1) - f a‖ + M + 1 := by
        simp only [norm_mul, fourier_apply, Circle.norm_coe, one_mul]
        linarith
  calc
    ‖(1 : ℂ) / (-2 * Real.pi * Complex.I * (k : ℂ))‖ * _
      ≤ ‖(1 : ℂ) / (-2 * Real.pi * Complex.I * (k : ℂ))‖ *
        (‖f (a + 1) - f a‖ + M + 1) := mul_le_mul_of_nonneg_left hbr (norm_nonneg _)
    _ = (‖f (a + 1) - f a‖ + M + 1) / (2 * Real.pi) * |(k : ℝ)| ^ (-1 : ℝ) := by
      simp only [norm_div, norm_one, norm_mul, norm_neg, Complex.norm_ofNat,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
        Complex.norm_I, mul_one, Complex.norm_intCast, Real.rpow_neg_one]
      ring

/-- Matching the values and first derivatives of a smooth unit cell yields cubic
Fourier decay. No matching of the second derivatives is needed. -/
theorem exists_fourierCoeff_liftIco_bound_three {f : ℝ → ℂ} {a : ℝ}
    (hf : ∀ x ∈ Icc a (a + 1), ContDiffAt ℝ 3 f x)
    (he : f a = f (a + 1)) (he' : deriv f a = deriv f (a + 1)) :
    ∃ K : ℝ, 0 < K ∧ ∀ k : ℤ, k ≠ 0 →
      ‖fourierCoeff (AddCircle.liftIco 1 a f) k‖ ≤ K * |(k : ℝ)| ^ (-3 : ℝ) := by
  have hd : ∀ x ∈ Icc a (a + 1), ContDiffAt ℝ 2 (deriv f) x :=
    fun x hx => (hf x hx).derivWithin (by norm_num)
  have hdd : ∀ x ∈ Icc a (a + 1), ContDiffAt ℝ 1 (deriv (deriv f)) x :=
    fun x hx => (hd x hx).derivWithin (by norm_num)
  obtain ⟨K, hK, hb⟩ := exists_fourierCoeffOn_unit_bound hdd
  have hint {g : ℝ → ℂ} (hg : ContinuousOn g (Icc a (a + 1))) :
      IntervalIntegrable g volume a (a + 1) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
    exact hg.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  refine ⟨K / (2 * Real.pi) ^ 2, by positivity, fun k hk => ?_⟩
  have hF := fourierCoeffOn_of_hasDerivAt (by linarith : a < a + 1) hk
    (fun x hx => (hf x (by simpa only [uIcc_of_le (by linarith : a ≤ a + 1)] using hx)).differentiableAt
      (by norm_num) |>.hasDerivAt) (hint fun x hx => (hd x hx).continuousAt.continuousWithinAt)
  have hD := fourierCoeffOn_of_hasDerivAt (by linarith : a < a + 1) hk
    (fun x hx => (hd x (by simpa only [uIcc_of_le (by linarith : a ≤ a + 1)] using hx)).differentiableAt
      (by norm_num) |>.hasDerivAt) (hint fun x hx => (hdd x hx).continuousAt.continuousWithinAt)
  norm_num only [Complex.ofReal_add, Complex.ofReal_one, add_sub_cancel_left] at hF hD
  rw [fourierCoeff_liftIco_eq, hF, hD]
  simp only [he, he', sub_self, mul_zero, zero_sub, norm_mul, norm_neg,
    norm_div, norm_one, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, Complex.norm_I, mul_one, Complex.norm_intCast,
    one_mul]
  calc
    (1 / (2 * Real.pi * |(k : ℝ)|)) *
        ((1 / (2 * Real.pi * |(k : ℝ)|)) * ‖fourierCoeffOn (by linarith : a < a + 1) (deriv (deriv f)) k‖)
      ≤ (1 / (2 * Real.pi * |(k : ℝ)|)) *
        ((1 / (2 * Real.pi * |(k : ℝ)|)) * (K * |(k : ℝ)| ^ (-1 : ℝ))) := by
          gcongr
          exact hb k hk
    _ = K / (2 * Real.pi) ^ 2 * |(k : ℝ)| ^ (-3 : ℝ) := by
      rw [Real.rpow_neg_one, Real.rpow_neg_ofNat]
      norm_num only [zpow_neg, zpow_ofNat, inv_pow]
      ring

end Riesz1
