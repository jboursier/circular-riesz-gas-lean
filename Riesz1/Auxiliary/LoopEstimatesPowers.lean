/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.VarianceTwoErrors

/-!
# Absorbing the localization and anchoring errors

The power arithmetic in the estimates part of Lemma 5.8.
-/

public section

noncomputable section

open scoped ENNReal

namespace Riesz1.Internal

/-- Absorb the two squared errors and the size-bias remainder, with constants
chosen independently of the scale and the envelope amplitude. -/
theorem loopEstimates_absorb {K a k ε A B D C₀ : ℝ}
    (hK : 1 ≤ K) (_ha : 0 ≤ a) (hk : 0 < k) (hε : 0 < ε)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D) (hC₀ : 0 ≤ C₀) (V : ℝ≥0∞) :
    3 * (ENNReal.ofReal (A * C₀ * K ^ (1 / 2 : ℝ)) ^ 2 +
      ENNReal.ofReal (B * C₀ * K ^ (a + k * ε)) ^ 2 +
      (ENNReal.ofReal (K ^ ε) * V + ENNReal.ofReal (D * C₀ ^ 2 * K ^ (-10 : ℝ)))) ≤
      ENNReal.ofReal ((3 * (A ^ 2 + B ^ 2 + D + 1)) * K ^ ((2 * k + 1) * ε)) * V +
        ENNReal.ofReal ((3 * (A ^ 2 + B ^ 2 + D + 1)) * C₀ ^ 2 *
          K ^ ((2 * k + 1) * ε) * (K + K ^ (2 * a))) := by
  have hK0 : 0 < K := by linarith
  let q := (2 * k + 1) * ε
  let T := A ^ 2 + B ^ 2 + D + 1
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hT : 1 ≤ T := by dsimp [T]; nlinarith [sq_nonneg A, sq_nonneg B]
  have hpow : 1 ≤ K ^ q := Real.one_le_rpow hK hq
  have hεq : K ^ ε ≤ K ^ q :=
    Real.rpow_le_rpow_of_exponent_le hK (by dsimp [q]; nlinarith)
  have hkq : K ^ (2 * k * ε) ≤ K ^ q :=
    Real.rpow_le_rpow_of_exponent_le hK (by dsimp [q]; nlinarith)
  have hneg : K ^ (-10 : ℝ) ≤ K := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hK (by norm_num : (-10 : ℝ) ≤ 1)
  have hhalf : (K ^ (1 / 2 : ℝ)) ^ 2 = K := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hK0.le]
    norm_num
  have hanchor : (K ^ (a + k * ε)) ^ 2 = K ^ (2 * a) * K ^ (2 * k * ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hK0.le, ← Real.rpow_add hK0]
    congr 1
    ring
  have hbase : K ≤ K ^ q * (K + K ^ (2 * a)) := by
    calc
      K ≤ K ^ q * K := le_mul_of_one_le_left hK0.le hpow
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) (by positivity)
  have hbase' : K ^ (2 * a) * K ^ (2 * k * ε) ≤ K ^ q * (K + K ^ (2 * a)) := by
    calc
      _ ≤ K ^ (2 * a) * K ^ q := mul_le_mul_of_nonneg_left hkq (by positivity)
      _ ≤ _ := by nlinarith [mul_nonneg (Real.rpow_nonneg hK0.le q) hK0.le]
  have herr : 3 * ((A * C₀ * K ^ (1 / 2 : ℝ)) ^ 2 +
      (B * C₀ * K ^ (a + k * ε)) ^ 2 + D * C₀ ^ 2 * K ^ (-10 : ℝ)) ≤
        3 * T * C₀ ^ 2 * K ^ q * (K + K ^ (2 * a)) := by
    have h1 := mul_le_mul_of_nonneg_left hbase (by positivity : 0 ≤ A ^ 2 * C₀ ^ 2)
    have h2 := mul_le_mul_of_nonneg_left hbase' (by positivity : 0 ≤ B ^ 2 * C₀ ^ 2)
    have h3 := mul_le_mul_of_nonneg_left (hneg.trans hbase) (by positivity : 0 ≤ D * C₀ ^ 2)
    have h4 : 0 ≤ C₀ ^ 2 * (K ^ q * (K + K ^ (2 * a))) := by positivity
    simp only [mul_pow, hhalf, hanchor] at *
    dsimp [T]
    nlinarith
  have hcoeff : 3 * K ^ ε ≤ 3 * T * K ^ q := by
    have ht : K ^ q ≤ T * K ^ q := le_mul_of_one_le_left (by positivity) hT
    linarith
  calc
    _ = ENNReal.ofReal (3 * K ^ ε) * V +
        ENNReal.ofReal (3 * ((A * C₀ * K ^ (1 / 2 : ℝ)) ^ 2 +
          (B * C₀ * K ^ (a + k * ε)) ^ 2 + D * C₀ ^ 2 * K ^ (-10 : ℝ))) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
        ENNReal.ofReal_add (add_nonneg (sq_nonneg _) (sq_nonneg _)) (by positivity),
        ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
        ENNReal.ofReal_pow (by positivity : 0 ≤ A * C₀ * K ^ (1 / 2 : ℝ)),
        ENNReal.ofReal_pow (by positivity : 0 ≤ B * C₀ * K ^ (a + k * ε))]
      norm_num only [ENNReal.ofReal_ofNat]
      ring
    _ ≤ _ := add_le_add (mul_le_mul' (ENNReal.ofReal_le_ofReal hcoeff) (le_refl V))
      (ENNReal.ofReal_le_ofReal herr)

end Riesz1.Internal

end
