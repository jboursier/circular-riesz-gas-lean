/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Tactic

/-!
# Fourier decay of a smooth fundamental cell with matching values

Derivatives need not match at the seam. One integration by parts still gives inverse
frequency decay for the continuous periodic lift.
-/

public section

open MeasureTheory Set

namespace Riesz1

/-- A smooth unit cell with equal endpoint values has Fourier coefficients bounded by `C/|k|`.
No equality of endpoint derivatives is required. -/
theorem exists_fourierCoeff_liftIco_bound {f : ℝ → ℂ} {a : ℝ}
    (hf : ∀ x ∈ Icc a (a + 1), ContDiffAt ℝ 1 f x) (he : f a = f (a + 1)) :
    ∃ K : ℝ, 0 < K ∧ ∀ k : ℤ, k ≠ 0 →
      ‖fourierCoeff (AddCircle.liftIco 1 a f) k‖ ≤ K * |(k : ℝ)| ^ (-1 : ℝ) := by
  have hdc : ContinuousOn (deriv f) (Icc a (a + 1)) :=
    fun x hx => ((hf x hx).derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hdc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM a ⟨le_rfl, by linarith⟩)
  have hdi : IntervalIntegrable (deriv f) volume a (a + 1) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
    exact hdc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  refine ⟨(M + 1) / (2 * Real.pi), by positivity, fun k hk => ?_⟩
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
  rw [fourierCoeff_liftIco_eq, hF]
  simp only [he, sub_self, mul_zero, zero_sub, norm_mul, norm_div, norm_one, norm_neg,
    Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    Complex.norm_I, mul_one, Complex.norm_intCast, Real.rpow_neg_one]
  norm_num only [Complex.ofReal_add, Complex.ofReal_one, add_sub_cancel_left, norm_one, one_mul]
  calc 1 / (2 * Real.pi * |(k : ℝ)|) * ‖fourierCoeffOn (by linarith : a < a + 1) (deriv f) k‖
      ≤ 1 / (2 * Real.pi * |(k : ℝ)|) * (M + 1) :=
        mul_le_mul_of_nonneg_left (hn.trans (by linarith)) (by positivity)
    _ = (M + 1) / (2 * Real.pi) * |(k : ℝ)|⁻¹ := by ring

end Riesz1
