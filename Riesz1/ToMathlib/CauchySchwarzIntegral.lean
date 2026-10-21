/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Cauchy–Schwarz inequality for integrals of real `L²` functions

For a measure `μ` and real functions `X, Y` in `L²(μ)`, the integral of the product is bounded by
the product of the `L²` norms: `|∫ X Y| ≤ (∫ X²)^{1/2} (∫ Y²)^{1/2}`. This is Hölder's inequality
with exponents `2` and `2`, applied to `|X|` and `|Y|`.

The main result is `Riesz1.abs_integral_mul_le_sqrt_integral_sq`.
-/

@[expose] public section

open MeasureTheory

namespace Riesz1

/-- The Cauchy–Schwarz inequality for the integral of a product of real `L²` functions. -/
theorem abs_integral_mul_le_sqrt_integral_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {X Y : α → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    |∫ a, X a * Y a ∂μ| ≤ Real.sqrt (∫ a, X a ^ 2 ∂μ) * Real.sqrt (∫ a, Y a ^ 2 ∂μ) := by
  have hXa : MemLp (fun a => ‖X a‖) (ENNReal.ofReal 2) μ := by
    rw [ENNReal.ofReal_ofNat]
    exact hX.norm
  have hYa : MemLp (fun a => ‖Y a‖) (ENNReal.ofReal 2) μ := by
    rw [ENNReal.ofReal_ofNat]
    exact hY.norm
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) (p := 2) (q := 2)
    Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun a => norm_nonneg (X a))
    (Filter.Eventually.of_forall fun a => norm_nonneg (Y a)) hXa hYa
  have hle : |∫ a, X a * Y a ∂μ| ≤ ∫ a, ‖X a‖ * ‖Y a‖ ∂μ := by
    refine (abs_integral_le_integral_abs).trans (le_of_eq ?_)
    congr 1
    funext a
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs] at hH
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, one_div]
  exact hle.trans (by simpa only [Real.norm_eq_abs, one_div] using hH)

end Riesz1

end
