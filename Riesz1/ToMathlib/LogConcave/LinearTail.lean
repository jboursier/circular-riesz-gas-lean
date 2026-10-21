/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.LogConcave.GapIBP

/-!
# Linear factors in exponential tails

Two scalar bounds for expectation errors under a tilt supported on a rare event.
-/

public section

namespace Riesz1

/-- Absorb the linear factor while retaining half the exponential decay. -/
theorem linear_tail_le_exp {c t u : ℝ} (hc : 0 < c) (ht : 0 ≤ t) (hu : u ≤ t) :
    t + 1 ≤ (2 / c + 1) * Real.exp (c * t) * Real.exp (-c * u / 2) := by
  have h1 := Real.add_one_le_exp (c * t / 2)
  have h2 : 1 ≤ Real.exp (c * t / 2) := Real.one_le_exp_iff.mpr (by positivity)
  have h3 : t ≤ (2 / c) * Real.exp (c * t / 2) := by
    apply (le_of_mul_le_mul_left _ hc)
    have he : c * ((2 / c) * Real.exp (c * t / 2)) = 2 * Real.exp (c * t / 2) := by
      field_simp
    rw [he]
    linarith
  calc t + 1 ≤ (2 / c + 1) * Real.exp (c * t / 2) := by nlinarith
    _ ≤ (2 / c + 1) * Real.exp (c * t - c * u / 2) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (by positivity)
    _ = (2 / c + 1) * Real.exp (c * t) * Real.exp (-c * u / 2) := by
      rw [sub_eq_add_neg, Real.exp_add]
      simp only [neg_div, neg_mul]
      ring

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
