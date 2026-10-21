/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-!
# Powers in the microscopic regularization and loop reduction

The exponent bookkeeping in Lemma 5.3 and
Proposition 5.6. These statements include `K = 1` and impose no
nonzero-exponent restriction. Constants in these inequalities are
absolute. No test profile occurs in their hypotheses.
-/

public section

namespace Riesz1.Internal

/-- Convert the far-piece estimate from `h = K⁻¹` to microscopic powers. -/
theorem reg_micro_far_powers {K : ℝ} (hK : 0 < K) (s α δ : ℝ) :
    K⁻¹ ^ (2 * (1 - s) - δ) * (K⁻¹ ^ (-s) + K⁻¹ ^ (-2 * (1 - s + α))) =
      K ^ δ * (K ^ (3 * s - 2) + K ^ (2 * α)) := by
  simp only [Real.inv_rpow hK.le, ← Real.rpow_neg hK.le]
  simp only [mul_add, ← Real.rpow_add hK]
  congr 2 <;> ring

/-- Squaring the analytic smoothing rate and restoring `K^s` leaves
exactly `K^(2α + 2δ)`. -/
theorem auxiliary_sobolev_error_powers {K : ℝ} (hK : 0 < K) (s α δ : ℝ) :
    K ^ s * (K⁻¹ ^ (s / 2 - α - δ)) ^ 2 = K ^ (2 * α + 2 * δ) := by
  rw [Real.inv_rpow hK.le, ← Real.rpow_neg hK.le, ← Real.rpow_natCast,
    ← Real.rpow_mul hK.le, ← Real.rpow_add hK]
  congr 1
  ring

/-- Both error powers in `reg-micro` are below the final variance-error
power, since `s ≤ 1`. -/
theorem auxiliary_micro_rate {K s α δ ε : ℝ} (hK : 1 ≤ K) (hs : s ≤ 1) (hδε : δ ≤ ε) :
    K ^ δ * (K ^ (2 * α) + K ^ (3 * s - 2)) ≤
      2 * K ^ (max (2 * s - 1) (2 * α) + ε) := by
  have hK0 : 0 < K := by linarith
  have hα : δ + 2 * α ≤ max (2 * s - 1) (2 * α) + ε :=
    add_le_add hδε (le_max_right _ _) |>.trans_eq (by ring)
  have hs' : δ + (3 * s - 2) ≤ max (2 * s - 1) (2 * α) + ε := by
    have := le_max_left (2 * s - 1) (2 * α)
    linarith
  rw [mul_add, ← Real.rpow_add hK0, ← Real.rpow_add hK0]
  linarith only [Real.rpow_le_rpow_of_exponent_le hK hα,
    Real.rpow_le_rpow_of_exponent_le hK hs']

/-- The differentiated-transport statistic contributes the same final
power after multiplication by the master-equation factor. -/
theorem auxiliary_derivative_rate {K s α δ ε : ℝ} (hK : 1 ≤ K) (hs : s ≤ 1) (hδε : δ ≤ ε) :
    K ^ (2 * s - 2) * (K ^ δ * (K ^ s + K ^ (2 * (1 - s + α)))) ≤
      2 * K ^ (max (2 * s - 1) (2 * α) + ε) := by
  have hK0 : 0 < K := by linarith
  have he : K ^ (2 * s - 2) * (K ^ δ * (K ^ s + K ^ (2 * (1 - s + α)))) =
      K ^ δ * (K ^ (2 * α) + K ^ (3 * s - 2)) := by
    simp only [mul_add, ← Real.rpow_add hK0]
    conv_rhs => rw [add_comm]
    congr 2 <;> ring
  rw [he]
  exact auxiliary_micro_rate hK hs hδε

/-- The derivative energy and the averaged quadratic-loop error have
the target power, including the critical value `2b = 1`. The analytic
logarithm, when present, is included in `K^δ`. -/
theorem auxiliary_energy_rate {K s α δ ε : ℝ} (hK : 1 ≤ K) (hδε : δ ≤ ε) :
    K ^ (2 * s - 1) * (K ^ δ * (1 + K ^ (2 * (1 - s + α) - 1))) ≤
      2 * K ^ (max (2 * s - 1) (2 * α) + ε) := by
  have hK0 : 0 < K := by linarith
  have h₁ : 2 * s - 1 + δ ≤ max (2 * s - 1) (2 * α) + ε :=
    add_le_add (le_max_left _ _) hδε
  have h₂ : 2 * α + δ ≤
      max (2 * s - 1) (2 * α) + ε := by
    have := le_max_right (2 * s - 1) (2 * α)
    linarith
  have he : K ^ (2 * s - 1) * (K ^ δ * (1 + K ^ (2 * (1 - s + α) - 1))) =
      K ^ (2 * s - 1 + δ) + K ^ (2 * α + δ) := by
    simp only [mul_add, mul_one, ← Real.rpow_add hK0]
    congr 2
    ring
  rw [he]
  linarith only [Real.rpow_le_rpow_of_exponent_le hK h₁,
    Real.rpow_le_rpow_of_exponent_le hK h₂]

/-- Absorb the small increase of the singularity exponent used at
`α = 0` and `α = s - 1`. -/
theorem reg_micro_endpoint_absorption {K α s δ ε : ℝ} (hK : 1 ≤ K)
    (hε : 0 ≤ ε) (hδ : 2 * δ ≤ ε / 2) :
    K ^ (ε / 2) * (K ^ (2 * (α + δ)) + K ^ (3 * s - 2)) ≤
      K ^ ε * (K ^ (2 * α) + K ^ (3 * s - 2)) := by
  have hK0 : 0 < K := by linarith
  simp only [mul_add, ← Real.rpow_add hK0]
  exact add_le_add
    (Real.rpow_le_rpow_of_exponent_le hK (by linarith))
    (Real.rpow_le_rpow_of_exponent_le hK (by linarith))

/-- A positive exponent increase avoiding both exceptional exponents
exists with an arbitrarily small prescribed power loss. -/
theorem reg_micro_endpoint_choice {s α ε : ℝ} (hα0 : s - 1 ≤ α)
    (hα1 : α < s / 2) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ s - 1 < α + δ ∧ α + δ < s / 2 ∧
      α + δ ≠ 0 ∧ 2 * δ < ε / 2 := by
  by_cases hα : α < 0
  · obtain ⟨δ, hδ0, hδ⟩ := exists_between
      (lt_min (by linarith : (0 : ℝ) < (s / 2 - α) / 2)
        (lt_min (by linarith : (0 : ℝ) < -α / 2) (by linarith : (0 : ℝ) < ε / 4)))
    refine ⟨δ, hδ0, by linarith, by linarith [lt_of_lt_of_le hδ (min_le_left _ _)],
      ?_, ?_⟩
    · have := lt_of_lt_of_le hδ (le_trans (min_le_right _ _) (min_le_left _ _))
      linarith
    · have := lt_of_lt_of_le hδ (le_trans (min_le_right _ _) (min_le_right _ _))
      linarith
  · obtain ⟨δ, hδ0, hδ⟩ := exists_between
      (lt_min (by linarith : (0 : ℝ) < (s / 2 - α) / 2) (by linarith : (0 : ℝ) < ε / 4))
    exact ⟨δ, hδ0, by linarith, by linarith [lt_of_lt_of_le hδ (min_le_left _ _)],
      by linarith, by linarith [lt_of_lt_of_le hδ (min_le_right _ _)]⟩

end Riesz1.Internal
