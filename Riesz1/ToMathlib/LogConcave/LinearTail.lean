/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.LogConcave.GapIBP

/-!
# Linear factors in exponential tails

A positive power of the scale in a decaying exponential dominates the linear scale.
-/

public section

namespace Riesz1

/-- A positive power of the scale in an exponential dominates the linear scale. -/
theorem exists_scale_exp_bound {c γ : ℝ} (hc : 0 < c) (hγ : 0 < γ) :
    ∃ K : ℝ, 0 < K ∧ ∀ L : ℝ, 0 < L → L * Real.exp (-c * L ^ γ) ≤ K := by
  obtain ⟨K, hK, hb⟩ := gap_exp_neg_mul_le hc (p := 1 / γ) (by positivity)
  refine ⟨K, hK, ?_⟩
  intro L hL
  have hh := mul_le_mul_of_nonneg_left (hb (L ^ γ) (Real.rpow_pos_of_pos hL γ)) hL.le
  have he : (L ^ γ) ^ (-(1 / γ)) = L⁻¹ := by
    rw [← Real.rpow_mul hL.le]
    have hc' : γ * -(1 / γ) = -1 := by field_simp
    rw [hc', Real.rpow_neg_one]
  rw [he] at hh
  simpa only [mul_left_comm L K, mul_inv_cancel₀ hL.ne', mul_one] using hh

end Riesz1
