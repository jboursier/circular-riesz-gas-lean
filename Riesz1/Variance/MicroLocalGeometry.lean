/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.MicroLocalIndependence
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Local pair geometry

Deterministic arc and inverse-block estimates for Lemma 5.3.
-/

public section

noncomputable section

open MeasureTheory Finset
open scoped ENNReal

namespace Riesz1

/-- Two particles at microscopic distance at most `R` have a forward or
backward block of length at most `R`. -/
theorem microLocal_close_blocks {N : ℕ+} (X : Configuration N) (i : ℤ)
    {k : ℕ} (hk : 0 < k) (hkN : k < (N : ℕ)) {R : ℝ}
    (hclose : dist (cyclicLift X i : UnitAddCircle)
      (cyclicLift X (i + k) : UnitAddCircle) ≤ R / (N : ℝ)) :
    blockLength X i k ≤ R ∨ blockLength X (i + k) ((N : ℕ) - k) ≤ R := by
  have hNr : (0 : ℝ) < (N : ℕ) := by exact_mod_cast N.pos
  have hkz : (0 : ℤ) < k := by exact_mod_cast hk
  have hkNz : (k : ℤ) < (N : ℕ) := by exact_mod_cast hkN
  let d := cyclicLift X (i + k) - cyclicLift X i
  have hd : 0 < d := sub_pos.mpr ((cyclicLift_strictMono X) (by omega))
  have hd1 : d < 1 := by
    have h := (cyclicLift_strictMono X) (show i + (k : ℤ) < i + (N : ℕ) by omega)
    rw [cyclicLift_add_N] at h
    dsimp [d]
    linarith
  have hback : blockLength X (i + k) ((N : ℕ) - k) = (N : ℝ) * (1 - d) := by
    have he : i + (k : ℤ) + (((N : ℕ) - k : ℕ) : ℤ) = i + (N : ℕ) := by
      rw [Nat.cast_sub hkN.le]
      ring
    simp only [blockLength, he, cyclicLift_add_N, d]
    ring
  rw [dist_comm, dist_eq_norm, ← AddCircle.coe_sub, UnitAddCircle.norm_eq] at hclose
  change |d - (round d : ℝ)| ≤ R / (N : ℝ) at hclose
  rcases lt_or_ge d (1 / 2) with hhalf | hhalf
  · have hr : round d = 0 := by
      rw [round_eq, Int.floor_eq_zero_iff, Set.mem_Ico]
      constructor <;> linarith
    rw [hr, Int.cast_zero, sub_zero, abs_of_pos hd] at hclose
    left
    change (N : ℝ) * d ≤ R
    nlinarith [(le_div_iff₀ hNr).mp hclose]
  · have hr : round d = 1 := by
      rw [round_eq, Int.floor_eq_iff]
      constructor <;> norm_num <;> linarith
    rw [hr, Int.cast_one, abs_of_neg (by linarith : d - 1 < 0)] at hclose
    right
    rw [hback]
    nlinarith [(le_div_iff₀ hNr).mp hclose]

/-- The indicator of a short positive length is bounded by its inverse square. -/
theorem microLocal_one_le_inverse {x R : ℝ} (hx : 0 < x) (hR : x ≤ R) :
    1 ≤ R ^ 2 * x ^ (-(2 : ℝ)) := by
  rw [Real.rpow_neg hx.le, Real.rpow_two, ← div_eq_mul_inv,
    le_div_iff₀ (sq_pos_of_pos hx)]
  nlinarith

/-- A close-pair indicator is dominated by the two inverse block squares. -/
theorem microLocal_pair_indicator {N : ℕ+} (X : Configuration N) (i : ℤ)
    {k : ℕ} (hk : 0 < k) (hkN : k < (N : ℕ)) {R : ℝ} :
    (if dist (cyclicLift X i : UnitAddCircle)
      (cyclicLift X (i + k) : UnitAddCircle) ≤ R / (N : ℝ) then (1 : ℝ) else 0) ≤
      R ^ 2 * (blockLength X i k ^ (-(2 : ℝ)) +
        blockLength X (i + k) ((N : ℕ) - k) ^ (-(2 : ℝ))) := by
  have ha := Real.rpow_nonneg (blockLength_pos X i hk).le (-(2 : ℝ))
  have hb := Real.rpow_nonneg (blockLength_pos X (i + k) (L := (N : ℕ) - k) (by omega)).le (-(2 : ℝ))
  split_ifs with h
  · rcases microLocal_close_blocks X i hk hkN h with hf | hb
    · have hh := microLocal_one_le_inverse (blockLength_pos X i hk) hf
      rw [mul_add]
      exact hh.trans (le_add_of_nonneg_right (mul_nonneg (sq_nonneg R) hb))
    · have hh := microLocal_one_le_inverse (blockLength_pos X (i + k) (L := (N : ℕ) - k) (by omega)) hb
      rw [mul_add]
      exact hh.trans (le_add_of_nonneg_left (mul_nonneg (sq_nonneg R) ha))
  · exact mul_nonneg (sq_nonneg R) (add_nonneg ha hb)

end Riesz1

end
