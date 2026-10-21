/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-!
# Power comparisons in block concentration

Elementary real inequalities used to simplify the local and full-system
tail exponents of Theorem 1.
-/

public section

namespace Riesz1.Internal

theorem rigidityBlocks_power_parameters {s ε : ℝ} (hs : 0 < s) (hε : 0 < ε) :
    0 < ε / (2 * (s + 2)) ∧ ε / (2 * (s + 2)) ≤ ε / 2 ∧
      (ε / (2 * (s + 2))) * (s + 2) = ε / 2 := by
  have hs2 : 0 < s + 2 := by linarith
  refine ⟨by positivity, ?_, ?_⟩
  · apply (div_le_iff₀ (by positivity : 0 < 2 * (s + 2))).mpr
    nlinarith [mul_pos hs hε]
  · field_simp

theorem rigidityBlocks_threshold_sq {s ε x : ℝ} (hx : 0 < x) :
    (x ^ (s / 2 + ε) / 3) ^ 2 = x ^ (s + 2 * ε) / 9 := by
  have hp : (x ^ (s / 2 + ε)) ^ 2 = x ^ (s + 2 * ε) := by
    rw [← Real.rpow_natCast (x ^ (s / 2 + ε)) 2, ← Real.rpow_mul hx.le]
    congr 1
    ring
  rw [div_pow, hp]
  norm_num

theorem rigidityBlocks_local_exponent {s ε b x : ℝ}
    (hs : 0 < s) (hε : 0 < ε) (hb : 0 < b) (hx : 1 ≤ x) :
    (b / (288 * (3 : ℝ) ^ ((1 + ε / (2 * (s + 2))) * (s + 2)))) *
        x ^ (ε / (2 * (s + 2))) ≤
      b * (3 * x + 1) * (2 * x + 1) * (x ^ (s / 2 + ε) / 3) ^ 2 /
        (32 * ((3 * x) ^ (1 + ε / (2 * (s + 2)))) ^ (s + 2)) := by
  let γ := ε / (2 * (s + 2))
  let q := (1 + γ) * (s + 2)
  have hx0 : 0 < x := by linarith
  have hp := rigidityBlocks_power_parameters hs hε
  have hγ : γ ≤ 3 * ε / 2 := by dsimp [γ]; linarith [hp.2.1]
  have hq : 2 + (s + 2 * ε) - q = 3 * ε / 2 := by
    dsimp only [q]
    have hγeq : γ * (s + 2) = ε / 2 := hp.2.2
    nlinarith [hγeq]
  have hR : ((3 * x) ^ (1 + γ)) ^ (s + 2) = (3 : ℝ) ^ q * x ^ q := by
    rw [← Real.rpow_mul (by positivity), Real.mul_rpow (by norm_num) hx0.le]
  have hquot : x ^ 2 * x ^ (s + 2 * ε) / x ^ q = x ^ (3 * ε / 2) := by
    rw [← Real.rpow_natCast x 2, ← Real.rpow_add hx0, ← Real.rpow_sub hx0]
    norm_num only [Nat.cast_ofNat]
    rw [hq]
  have heq : b * x ^ 2 * (x ^ (s / 2 + ε) / 3) ^ 2 /
      (32 * ((3 * x) ^ (1 + γ)) ^ (s + 2)) =
      b / (288 * (3 : ℝ) ^ q) * x ^ (3 * ε / 2) := by
    rw [rigidityBlocks_threshold_sq hx0, hR]
    calc b * x ^ 2 * (x ^ (s + 2 * ε) / 9) / (32 * ((3 : ℝ) ^ q * x ^ q)) =
        b / (288 * (3 : ℝ) ^ q) * (x ^ 2 * x ^ (s + 2 * ε) / x ^ q) := by ring
      _ = _ := by rw [hquot]
  have hprod : x ^ 2 ≤ (3 * x + 1) * (2 * x + 1) := by nlinarith [sq_nonneg x]
  calc b / (288 * (3 : ℝ) ^ q) * x ^ γ ≤
        b / (288 * (3 : ℝ) ^ q) * x ^ (3 * ε / 2) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx hγ) (by positivity)
    _ = b * x ^ 2 * (x ^ (s / 2 + ε) / 3) ^ 2 /
        (32 * ((3 * x) ^ (1 + γ)) ^ (s + 2)) := heq.symm
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have h := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hprod hb.le) (sq_nonneg (x ^ (s / 2 + ε) / 3))
      nlinarith only [h]

theorem rigidityBlocks_full_exponent {s ε b x n m : ℝ}
    (hs : 0 < s) (hε : 0 < ε) (hb : 0 < b) (hx : 1 ≤ x)
    (hn : 0 < n) (hnx : n ≤ 3 * x) (hxm : x ≤ m) :
    (b / (72 * (3 : ℝ) ^ (s + 1))) * x ^ (ε / (2 * (s + 2))) ≤
      b * n * m * (x ^ (s / 2 + ε) / 3) ^ 2 / (8 * n ^ (s + 2)) := by
  have hx0 : 0 < x := by linarith
  have hp := rigidityBlocks_power_parameters hs hε
  have hγ : ε / (2 * (s + 2)) ≤ 2 * ε := by linarith [hp.2.1]
  have hquot : x * x ^ (s + 2 * ε) / x ^ (s + 1) = x ^ (2 * ε) := by
    calc x * x ^ (s + 2 * ε) / x ^ (s + 1) =
        x ^ (1 : ℝ) * x ^ (s + 2 * ε) / x ^ (s + 1) := by rw [Real.rpow_one]
      _ = _ := by
        rw [← Real.rpow_add hx0, ← Real.rpow_sub hx0]
        congr 1
        ring
  have heq : b * x * (x ^ (s / 2 + ε) / 3) ^ 2 / (8 * (3 * x) ^ (s + 1)) =
      b / (72 * (3 : ℝ) ^ (s + 1)) * x ^ (2 * ε) := by
    rw [rigidityBlocks_threshold_sq hx0, Real.mul_rpow (by norm_num) hx0.le]
    calc b * x * (x ^ (s + 2 * ε) / 9) /
        (8 * ((3 : ℝ) ^ (s + 1) * x ^ (s + 1))) =
        b / (72 * (3 : ℝ) ^ (s + 1)) * (x * x ^ (s + 2 * ε) / x ^ (s + 1)) := by ring
      _ = _ := by rw [hquot]
  have hm0 : 0 < m := lt_of_lt_of_le hx0 hxm
  have hnR : n ^ (s + 1) ≤ (3 * x) ^ (s + 1) :=
    Real.rpow_le_rpow hn.le hnx (by linarith)
  have hnpow : n ^ (s + 2) = n * n ^ (s + 1) := by
    rw [show s + 2 = 1 + (s + 1) by ring, Real.rpow_add hn, Real.rpow_one]
  calc b / (72 * (3 : ℝ) ^ (s + 1)) * x ^ (ε / (2 * (s + 2))) ≤
        b / (72 * (3 : ℝ) ^ (s + 1)) * x ^ (2 * ε) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx hγ) (by positivity)
    _ = b * x * (x ^ (s / 2 + ε) / 3) ^ 2 / (8 * (3 * x) ^ (s + 1)) := heq.symm
    _ ≤ b * m * (x ^ (s / 2 + ε) / 3) ^ 2 / (8 * n ^ (s + 1)) := by
      apply div_le_div₀ (by positivity) _ (by positivity) (mul_le_mul_of_nonneg_left hnR (by norm_num))
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hxm hb.le) (sq_nonneg _)
    _ = _ := by rw [hnpow]; field_simp

end Riesz1.Internal
