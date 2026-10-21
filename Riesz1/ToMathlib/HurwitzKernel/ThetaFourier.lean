/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Tactic

/-!
# Fourier coefficients of the Hurwitz theta kernel

The cosine theta kernel has an absolutely convergent Fourier series at every
positive time. Integrating that series gives its Gaussian Fourier coefficients.
This is the scalar Fourier calculation needed in a Mellin representation of
the Riesz kernel.
-/

public section

open MeasureTheory Complex

namespace Riesz1

/-- The Fourier series of the cosine theta kernel, with circle-valued spatial
parameter and the project's Fourier convention. -/
lemma hasSum_cosKernel_fourier (x : UnitAddCircle) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ => (Real.exp (-Real.pi * (n : ℝ) ^ 2 * t) : ℂ) * fourier n x)
      (HurwitzZeta.cosKernel x t : ℂ) := by
  induction x using QuotientAddGroup.induction_on with
  | H a =>
    simpa only [fourier_coe_apply, ofReal_one, div_one, mul_comm, mul_left_comm,
      mul_assoc] using HurwitzZeta.hasSum_int_cosKernel a ht

/-- The normalized Fourier coefficients of the cosine theta kernel. -/
theorem fourierCoeff_cosKernel (t : ℝ) (ht : 0 < t) (k : ℤ) :
    fourierCoeff (fun x : UnitAddCircle => (HurwitzZeta.cosKernel x t : ℂ)) k =
      (Real.exp (-Real.pi * (k : ℝ) ^ 2 * t) : ℂ) := by
  let a (n : ℤ) : ℂ := Real.exp (-Real.pi * (n : ℝ) ^ 2 * t)
  let F (n : ℤ) (x : UnitAddCircle) : ℂ := a n * fourier n x
  have hi (n : ℤ) : Integrable (F n) AddCircle.haarAddCircle :=
    (continuous_const.mul (fourier n).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hnorm (n : ℤ) : ∫ x : UnitAddCircle, ‖F n x‖ ∂AddCircle.haarAddCircle =
      Real.exp (-Real.pi * (n : ℝ) ^ 2 * t) := by
    simp only [F, a, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le, fourier_apply, Circle.norm_coe, mul_one]
    simp
  have hs : Summable (fun n : ℤ => ∫ x : UnitAddCircle, ‖F n x‖ ∂AddCircle.haarAddCircle) := by
    simp_rw [hnorm]
    simpa only [add_zero] using (HurwitzZeta.hasSum_int_evenKernel 0 ht).summable
  have hbound (n : ℤ) :
      (∫ x : UnitAddCircle, ‖fourier (-k) x • F n x‖ ∂AddCircle.haarAddCircle) =
        ∫ x : UnitAddCircle, ‖F n x‖ ∂AddCircle.haarAddCircle := by
    congr 1
    funext x
    simp only [norm_smul, fourier_apply, Circle.norm_coe, one_mul]
  calc
    _ = ∫ x : UnitAddCircle, ∑' n : ℤ, fourier (-k) x • F n x ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      apply ae_of_all
      intro x
      exact ((hasSum_cosKernel_fourier x ht).mul_left (fourier (-k) x)).tsum_eq.symm
    _ = ∑' n : ℤ, fourierCoeff (F n) k := by
      exact integral_tsum_of_summable_integral_norm (fun n => (hi n).fourier_smul (-k))
        (by simpa only [hbound] using hs) |>.symm
    _ = a k := by
      simp only [F, fourierCoeff.const_mul, fourierCoeff_fourier]
      simp [Pi.single_apply]

/-- The Fourier coefficients of the Gaussian periodization. -/
theorem fourierCoeff_evenKernel (t : ℝ) (ht : 0 < t) (k : ℤ) :
    fourierCoeff (fun x : UnitAddCircle => (HurwitzZeta.evenKernel x t : ℂ)) k =
      ((1 / t ^ (1 / 2 : ℝ) * Real.exp (-Real.pi * (k : ℝ) ^ 2 / t) : ℝ) : ℂ) := by
  have he : (fun x : UnitAddCircle => (HurwitzZeta.evenKernel x t : ℂ)) =
      (fun x : UnitAddCircle => ((1 / t ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
        (HurwitzZeta.cosKernel x (1 / t) : ℂ)) := by
    funext x
    rw [HurwitzZeta.evenKernel_functional_equation, ofReal_mul]
  rw [he, fourierCoeff.const_mul, fourierCoeff_cosKernel (1 / t) (by positivity)]
  push_cast
  congr 2
  rw [mul_one_div]

/-- The cosine theta kernel is continuous in its circle variable at positive
time. The proof uses uniform absolute convergence of its Fourier series. -/
theorem continuous_cosKernel_complex (t : ℝ) (ht : 0 < t) :
    Continuous (fun x : UnitAddCircle => (HurwitzZeta.cosKernel x t : ℂ)) := by
  have hs : Summable (fun n : ℤ => Real.exp (-Real.pi * (n : ℝ) ^ 2 * t)) := by
    simpa only [add_zero] using (HurwitzZeta.hasSum_int_evenKernel 0 ht).summable
  have hcont : Continuous (fun x : UnitAddCircle => ∑' n : ℤ,
      (Real.exp (-Real.pi * (n : ℝ) ^ 2 * t) : ℂ) * fourier n x) := by
    apply continuous_tsum (f := fun (n : ℤ) (x : UnitAddCircle) =>
      (Real.exp (-Real.pi * (n : ℝ) ^ 2 * t) : ℂ) * fourier n x)
      (fun n => continuous_const.mul (fourier n).continuous) hs
    intro n x
    simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      fourier_apply, Circle.norm_coe, mul_one, le_refl]
  exact hcont.congr (fun x => (hasSum_cosKernel_fourier x ht).tsum_eq)

/-- Integrability of the cosine theta kernel at positive time. -/
theorem integrable_cosKernel_complex (t : ℝ) (ht : 0 < t) :
    Integrable (fun x : UnitAddCircle => (HurwitzZeta.cosKernel x t : ℂ))
      AddCircle.haarAddCircle :=
  (continuous_cosKernel_complex t ht).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Integrability of the Gaussian periodization at positive time. -/
theorem integrable_evenKernel_complex (t : ℝ) (ht : 0 < t) :
    Integrable (fun x : UnitAddCircle => (HurwitzZeta.evenKernel x t : ℂ))
      AddCircle.haarAddCircle := by
  have h := (integrable_cosKernel_complex (1 / t) (by positivity)).const_mul
    ((1 / t ^ (1 / 2 : ℝ) : ℝ) : ℂ)
  convert h using 1
  funext x
  rw [HurwitzZeta.evenKernel_functional_equation, ofReal_mul]

/-- The Gaussian periodization has spatial mean `t^(-1/2)`. -/
theorem integral_evenKernel (t : ℝ) (ht : 0 < t) :
    ∫ x : UnitAddCircle, HurwitzZeta.evenKernel x t ∂AddCircle.haarAddCircle =
      1 / t ^ (1 / 2 : ℝ) := by
  have h := fourierCoeff_evenKernel t ht 0
  simp only [fourierCoeff, neg_zero, fourier_zero, one_smul, Int.cast_zero,
    zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_div,
    Real.exp_zero, mul_one, integral_complex_ofReal] at h
  exact ofReal_injective h

/-- Absolute deviation from the spatial mean is bounded by the deviation at
zero. This estimate is useful for the small-time Mellin integral. -/
theorem abs_cosKernel_sub_one_le (x : UnitAddCircle) (t : ℝ) (ht : 0 < t) :
    |HurwitzZeta.cosKernel x t - 1| ≤ HurwitzZeta.cosKernel 0 t - 1 := by
  induction x using QuotientAddGroup.induction_on with
  | H a =>
    have h0 : HasSum (fun n : ℕ => 2 * Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * t))
        (HurwitzZeta.cosKernel 0 t - 1) := by
      simpa only [mul_zero, zero_mul, Real.cos_zero, mul_one, AddCircle.coe_zero] using
        HurwitzZeta.hasSum_nat_cosKernel₀ 0 ht
    rw [← (HurwitzZeta.hasSum_nat_cosKernel₀ a ht).tsum_eq, ← Real.norm_eq_abs]
    apply tsum_of_norm_bounded h0
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
      abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_right (by norm_num : (0 : ℝ) ≤ 2) (Real.abs_cos_le_one _))
      (Real.exp_pos _).le

/-- The Gaussian periodization is nonnegative. -/
theorem evenKernel_nonneg (x : UnitAddCircle) (t : ℝ) (ht : 0 < t) :
    0 ≤ HurwitzZeta.evenKernel x t := by
  induction x using QuotientAddGroup.induction_on with
  | H a =>
    rw [← (HurwitzZeta.hasSum_int_evenKernel a ht).tsum_eq]
    exact tsum_nonneg (fun n => (Real.exp_pos _).le)

/-- A uniform bound for the theta kernel after subtracting its spatial mean. -/
theorem abs_evenKernel_sub_le (x : UnitAddCircle) (t : ℝ) (ht : 0 < t) :
    |HurwitzZeta.evenKernel x t - 1 / t ^ (1 / 2 : ℝ)| ≤
      HurwitzZeta.evenKernel 0 t - 1 / t ^ (1 / 2 : ℝ) := by
  rw [HurwitzZeta.evenKernel_functional_equation x,
    HurwitzZeta.evenKernel_functional_equation 0]
  have hpos : 0 ≤ 1 / t ^ (1 / 2 : ℝ) := by positivity
  calc
    _ = (1 / t ^ (1 / 2 : ℝ)) * |HurwitzZeta.cosKernel x (1 / t) - 1| := by
      rw [← mul_sub_one, abs_mul, abs_of_nonneg hpos]
    _ ≤ (1 / t ^ (1 / 2 : ℝ)) * (HurwitzZeta.cosKernel 0 (1 / t) - 1) :=
      mul_le_mul_of_nonneg_left (abs_cosKernel_sub_one_le x (1 / t) (by positivity)) hpos
    _ = _ := by ring

end Riesz1
