/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-! # Comparing expectations by a second moment -/

public section

open MeasureTheory
open scoped ENNReal

namespace Riesz1

/-- The real second norm, with its finiteness certificate, is the square
root of the second moment. -/
theorem eLpNorm_two_toReal_eq_sqrt_integral_sq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {H : Ω → ℝ} (hH : MemLp H 2 μ) :
    (eLpNorm H 2 μ).toReal = Real.sqrt (∫ x, H x ^ 2 ∂μ) := by
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hH]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun _ => sq_nonneg _) _)]
  simpa only [one_div] using (Real.sqrt_eq_rpow (∫ x, H x ^ 2 ∂μ)).symm

/-- Taking square roots of a two-term second-moment bound. -/
theorem eLpNorm_two_toReal_le_add_of_integral_sq_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {H : Ω → ℝ} (hH : MemLp H 2 μ)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hb : (∫ x, H x ^ 2 ∂μ) ≤ A ^ 2 + B ^ 2) :
    (eLpNorm H 2 μ).toReal ≤ A + B := by
  rw [eLpNorm_two_toReal_eq_sqrt_integral_sq hH]
  have hi : 0 ≤ ∫ x, H x ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  nlinarith [Real.sq_sqrt hi, Real.sqrt_nonneg (∫ x, H x ^ 2 ∂μ)]

/-- A one-Lipschitz function changes expectations by at most the second
norm of the difference on a probability space. -/
theorem abs_integral_comp_sub_le_eLpNorm_two {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {F G : Ω → ℝ}
    (hFG : MemLp (fun x => F x - G x) 2 μ) {f : ℝ → ℝ}
    (hf : LipschitzWith 1 f) (hF : Integrable (fun x => f (F x)) μ)
    (hG : Integrable (fun x => f (G x)) μ) :
    |(∫ x, f (F x) ∂μ) - ∫ x, f (G x) ∂μ| ≤
      (eLpNorm (fun x => F x - G x) 2 μ).toReal := by
  have hnorm : Integrable (fun x => ‖F x - G x‖) μ :=
    (hFG.integrable one_le_two).norm
  have h1 : (eLpNorm (fun x => F x - G x) 1 μ).toReal =
      ∫ x, ‖F x - G x‖ ∂μ := by
    rw [MemLp.eLpNorm_eq_integral_rpow_norm one_ne_zero ENNReal.one_ne_top
      (hFG.mono_exponent one_le_two)]
    simp only [ENNReal.toReal_one, inv_one, Real.rpow_one]
    exact ENNReal.toReal_ofReal (integral_nonneg fun _ => norm_nonneg _)
  rw [← integral_sub hF hG, ← Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  apply (integral_mono (hF.sub hG).norm hnorm ?_).trans
  · rw [← h1]
    exact ENNReal.toReal_mono hFG.eLpNorm_ne_top
      (eLpNorm_le_eLpNorm_of_exponent_le one_le_two)
  · intro x
    simpa only [Pi.sub_apply, Real.dist_eq, NNReal.coe_one, one_mul, Real.norm_eq_abs] using
      hf.dist_le_mul (F x) (G x)

end Riesz1
