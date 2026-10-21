/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.SmoothingVariance

/-!
# Scale and exponent calculations for the loop error

The deterministic power comparisons in the proof of Theorem 3.
The estimates include `K = 1` and the endpoint `α = s - 1`.
-/

public section

namespace Riesz1

/-- The smoothing radius `cltDelta` is admissible for Proposition 5.9. -/
theorem cltDelta_ge_inv (P : Parameters) (N : ℕ+) (a : Scale)
    (hK : 1 ≤ (N : ℝ) * a.val) :
    ((N : ℝ) * a.val)⁻¹ ≤ cltDelta P N a := by
  rw [← Real.rpow_neg_one]
  unfold cltDelta
  apply Real.rpow_le_rpow_of_exponent_le hK
  have hs := P.property.2.1
  have hd : (2 - P.val.2) / (4 + P.val.2) ≤ 1 :=
    (div_le_one (by linarith)).mpr (by linarith)
  linarith

/-- The exponent after taking the variance square root and applying the
normalization in `Error²` is exactly the exponent of the paper. -/
theorem errorTwo_exponent (s α : ℝ) :
    -1 + s / 2 + max (1 / 2) (1 - s + α) =
      max ((s - 1) / 2) (α - s / 2) := by
  rw [add_max]
  congr 1 <;> ring

/-- The maximum-power form of Proposition 5.9 implies the two-power form
used in the proof of Theorem 3, without changing the loss or the constant. -/
theorem errorTwo_loop_power_bound {K : ℝ} (hK : 1 ≤ K) (b τ : ℝ) :
    K ^ (2 * τ + max 1 (2 * b)) ≤ K ^ (2 * τ) * (K + K ^ (2 * b)) := by
  rw [Real.rpow_add (by linarith : 0 < K)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rcases le_total (1 : ℝ) (2 * b) with hb | hb
  · rw [max_eq_right hb]
    exact le_add_of_nonneg_left (by linarith)
  · rw [max_eq_left hb, Real.rpow_one]
    exact le_add_of_nonneg_right (by positivity)

/-- The a-priori variance power is bounded by the loop-error power sum. -/
theorem errorTwo_derivative_power_bound {K s : ℝ} (hK : 1 ≤ K) (hs : s ≤ 1)
    (b ε : ℝ) :
    K ^ (ε + max (2 * b) s) ≤ K ^ ε * (K + K ^ (2 * b)) := by
  rw [Real.rpow_add (by linarith : 0 < K)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rcases le_total s (2 * b) with hb | hb
  · rw [max_eq_left hb]
    exact le_add_of_nonneg_left (by linarith)
  · rw [max_eq_right hb]
    calc
      K ^ s ≤ K ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hK hs
      _ ≤ K + K ^ (2 * b) := by
        rw [Real.rpow_one]
        exact le_add_of_nonneg_right (by positivity)

/-- Square root of the sum of the two variance powers. -/
theorem errorTwo_sqrt_powers {K : ℝ} (hK : 1 ≤ K) (b : ℝ) :
    Real.sqrt (K + K ^ (2 * b)) ≤ 2 * K ^ max (1 / 2) b := by
  have hK0 : 0 ≤ K := by linarith
  have h1 : K ≤ (K ^ max (1 / 2) b) ^ 2 := by
    rw [← Real.rpow_mul_natCast hK0]
    calc
      K = K ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ K ^ (max (1 / 2) b * 2) :=
        Real.rpow_le_rpow_of_exponent_le hK (by linarith [le_max_left (1 / 2 : ℝ) b])
  have h2 : K ^ (2 * b) ≤ (K ^ max (1 / 2) b) ^ 2 := by
    rw [← Real.rpow_mul_natCast hK0]
    apply Real.rpow_le_rpow_of_exponent_le hK
    linarith [le_max_right (1 / 2 : ℝ) b]
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity, ?_⟩
  nlinarith [sq_nonneg (K ^ max (1 / 2) b)]

/-- The square root and normalization of the displayed joint variance rate
in the proof of Theorem 3 have the displayed error exponent. -/
theorem errorTwo_scaled_sqrt {K : ℝ} (hK : 1 ≤ K) (s α τ : ℝ) :
    K ^ (-1 + s / 2) * Real.sqrt (K ^ (2 * τ) * (K + K ^ (2 * (1 - s + α)))) ≤
      2 * K ^ (max ((s - 1) / 2) (α - s / 2) + τ) := by
  have hK0 : 0 < K := by linarith
  have hsqrt : Real.sqrt (K ^ (2 * τ)) = K ^ τ := by
    rw [show 2 * τ = τ * (2 : ℕ) by ring,
      Real.rpow_mul_natCast hK0.le, Real.sqrt_sq (Real.rpow_nonneg hK0.le _)]
  rw [Real.sqrt_mul (Real.rpow_nonneg hK0.le _), hsqrt]
  calc
    _ ≤ K ^ (-1 + s / 2) * (K ^ τ * (2 * K ^ max (1 / 2) (1 - s + α))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (errorTwo_sqrt_powers hK (1 - s + α)) (by positivity)) (by positivity)
    _ = 2 * K ^ (max ((s - 1) / 2) (α - s / 2) + τ) := by
      rw [show K ^ (-1 + s / 2) * (K ^ τ * (2 * K ^ max (1 / 2) (1 - s + α))) =
        2 * ((K ^ (-1 + s / 2) * K ^ max (1 / 2) (1 - s + α)) * K ^ τ) by ring,
        ← Real.rpow_add hK0, errorTwo_exponent, ← Real.rpow_add hK0]

end Riesz1
