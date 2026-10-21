/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.Mollifier.RegularizationSobolev

/-!
# A two-term inequality for the homogeneous Fourier seminorm

The extended-valued squared seminorm obeys the squared triangle inequality
with factor two, at every real order and without finiteness assumptions.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace Riesz1

theorem circleSobolevSq_le_two_mul_add (r : ℝ)
    (f g : {f : UnitAddCircle → ℂ // MemLp f 2 volume}) :
    circleSobolevSq r f ≤ 2 * (circleSobolevSq r g +
      circleSobolevSq r (subL2 f g)) := by
  unfold circleSobolevSq
  rw [mul_add, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro k
  by_cases hk : k = 0
  · simp only [hk, ite_true, mul_zero, add_zero, le_refl]
  · simp only [hk, ite_false, fourierCoeff_subL2]
    have htwo (x : ℝ) : (2 : ℝ≥0∞) * ENNReal.ofReal x = ENNReal.ofReal (2 * x) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    rw [htwo, htwo,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hn : ‖fourierCoeff f.val k‖ ≤ ‖fourierCoeff g.val k‖ +
        ‖fourierCoeff f.val k - fourierCoeff g.val k‖ := by
      calc _ = ‖fourierCoeff g.val k + (fourierCoeff f.val k - fourierCoeff g.val k)‖ := by
              congr 1
              ring
        _ ≤ _ := norm_add_le _ _
    have hs : ‖fourierCoeff f.val k‖ ^ 2 ≤
        2 * (‖fourierCoeff g.val k‖ ^ 2 + ‖fourierCoeff f.val k - fourierCoeff g.val k‖ ^ 2) := by
      nlinarith [norm_nonneg (fourierCoeff f.val k),
        norm_nonneg (fourierCoeff g.val k),
        norm_nonneg (fourierCoeff f.val k - fourierCoeff g.val k),
        sq_nonneg (‖fourierCoeff g.val k‖ - ‖fourierCoeff f.val k - fourierCoeff g.val k‖)]
    nlinarith [mul_le_mul_of_nonneg_left hs
      (Real.rpow_nonneg (abs_nonneg (k : ℝ)) (2 * r))]

end Riesz1
