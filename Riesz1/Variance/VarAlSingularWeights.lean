/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriComparisonWeights
public import Riesz1.Auxiliary.GradientSplittingZWeights

/-!
# Spatial envelopes and augmented label weights

The deterministic weight conversion in the proof of Proposition 5.9.
The comparison loss is uniform in the scale.
-/

@[expose] public section

noncomputable section

namespace Riesz1

/-- A denominator comparison with a loss exponent independent of epsilon. -/
theorem varAlSingular_inverse_power {K ε d r p : ℝ} (hK : 1 ≤ K) (hε : 0 ≤ ε)
    (hd : 0 ≤ d) (hr : 0 < r) (hp : 0 ≤ p) (hp3 : p ≤ 3)
    (hcomp : 1 + d ≤ 2 * K ^ ε * r) :
    r ^ (-p) ≤ 8 * K ^ (3 * ε) / (1 + d) ^ p := by
  have hK0 : 0 < K := by linarith
  have hden : 0 < (1 + d) ^ p := Real.rpow_pos_of_pos (by linarith) _
  have hpow := Real.rpow_le_rpow (by linarith : 0 ≤ 1 + d) hcomp hp
  have h2 : (2 : ℝ) ^ p ≤ 8 := by
    calc (2 : ℝ) ^ p ≤ 2 ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hp3
      _ = 8 := by norm_num
  have hKe : (K ^ ε) ^ p ≤ K ^ (3 * ε) := by
    rw [← Real.rpow_mul hK0.le]
    apply Real.rpow_le_rpow_of_exponent_le hK
    nlinarith
  have hh : (1 + d) ^ p ≤ (8 * K ^ (3 * ε)) * r ^ p := by
    calc (1 + d) ^ p ≤ (2 * K ^ ε * r) ^ p := hpow
      _ = (2 ^ p * (K ^ ε) ^ p) * r ^ p := by
        rw [Real.mul_rpow (by positivity) hr.le, Real.mul_rpow (by norm_num) (by positivity)]
      _ ≤ (8 * K ^ (3 * ε)) * r ^ p :=
        mul_le_mul_of_nonneg_right (mul_le_mul h2 hKe (by positivity) (by norm_num)) (by positivity)
  rw [Real.rpow_neg hr.le, inv_eq_one_div,
    div_le_div_iff₀ (Real.rpow_pos_of_pos hr _) hden]
  simpa only [one_mul, mul_comm] using hh

/-- The near-origin spatial weight becomes the first comparison summand.
The far weight becomes the second summand. The last spatial term becomes
the added third summand. -/
theorem varAlSingular_weights {N : ℕ+} {K s b ε δ : ℝ} (i : Fin (N : ℕ))
    (hK : 1 ≤ K) (hs0 : 0 < s) (hs1 : s < 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    (hlo : K ^ (-ε) * (labelDistToOne N i : ℝ) ≤ δ)
    (hhi : δ ≤ K ^ ε * (labelDistToOne N i : ℝ)) :
    K⁻¹ * (if δ / K < 1 then (max (δ / K) K⁻¹) ^ (-(1 + b))
      else (δ / K) ^ (s - 3)) + K ^ b / (1 + δ) ^ (1 + s / 2) ≤
      8 * K ^ (3 * ε) * augmentedComparisonWeight N K s b ε i := by
  have hK0 : 0 < K := by linarith
  let d : ℝ := labelDistToOne N i
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have he : 1 ≤ K ^ ε := Real.one_le_rpow hK hε
  have hdδ : d ≤ K ^ ε * δ := by
    calc
      d = K ^ ε * (K ^ (-ε) * d) := by
        rw [← mul_assoc, ← Real.rpow_add hK0]
        simp
      _ ≤ K ^ ε * δ := mul_le_mul_of_nonneg_left hlo (by positivity)
  have hnear : 1 + d ≤ 2 * K ^ ε * max δ 1 := by
    have ha : 1 ≤ K ^ ε * max δ 1 := by
      exact one_le_mul_of_one_le_of_one_le he (le_max_right _ _)
    have hc : d ≤ K ^ ε * max δ 1 := hdδ.trans
      (mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity))
    linarith
  have hlast : K ^ b / (1 + δ) ^ (1 + s / 2) ≤
      8 * K ^ (3 * ε) * (K ^ b / (1 + d) ^ (1 + s / 2)) := by
    have hc : 1 + d ≤ 2 * K ^ ε * (1 + δ) := by
      have hm : K ^ ε * δ ≤ K ^ ε * (1 + δ) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      nlinarith
    have hh := varAlSingular_inverse_power hK hε hd (by linarith : 0 < 1 + δ)
      (by linarith : 0 ≤ 1 + s / 2) (by linarith : 1 + s / 2 ≤ 3) hc
    rw [Real.rpow_neg (by linarith : 0 ≤ 1 + δ)] at hh
    have := mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hK0.le b)
    simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
  have hmain : K⁻¹ * (if δ / K < 1 then (max (δ / K) K⁻¹) ^ (-(1 + b))
      else (δ / K) ^ (s - 3)) ≤ 8 * K ^ (3 * ε) * comparisonWeight N K s b ε i := by
    by_cases hn : δ / K < 1
    · rw [ite_eq_left hn]
      have hdK : d ≤ K ^ (1 + ε) := by
        rw [Real.rpow_add hK0, Real.rpow_one]
        have : δ < K := (div_lt_one hK0).mp hn
        nlinarith [Real.rpow_pos_of_pos hK0 ε]
      have hw : K ^ b / (1 + d) ^ (1 + b) ≤ comparisonWeight N K s b ε i := by
        unfold comparisonWeight
        rw [ite_eq_left hdK]
        exact le_add_of_nonneg_right (by split_ifs <;> positivity)
      have hm : max (δ / K) K⁻¹ = max δ 1 / K := by
        simpa only [one_div] using (max_div_div_right hK0.le (a := δ) (b := 1))
      have hh := varAlSingular_inverse_power hK hε hd
        (lt_of_lt_of_le zero_lt_one (le_max_right δ 1))
        (by linarith : 0 ≤ 1 + b) (by linarith : 1 + b ≤ 3) hnear
      have heq : K⁻¹ * (max (δ / K) K⁻¹) ^ (-(1 + b)) =
          K ^ b * (max δ 1) ^ (-(1 + b)) := by
        rw [hm, Real.div_rpow (by positivity) hK0.le, div_eq_mul_inv,
          ← Real.rpow_neg hK0.le, neg_neg, ← Real.rpow_neg_one,
          mul_left_comm, ← Real.rpow_add hK0]
        rw [show -1 + (1 + b) = b by ring]
        ring
      rw [heq]
      calc K ^ b * (max δ 1) ^ (-(1 + b)) ≤
          K ^ b * (8 * K ^ (3 * ε) / (1 + d) ^ (1 + b)) :=
            mul_le_mul_of_nonneg_left hh (by positivity)
        _ = 8 * K ^ (3 * ε) * (K ^ b / (1 + d) ^ (1 + b)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hw (by positivity)
    · rw [ite_eq_right hn]
      have hδK : K ≤ δ := (one_le_div hK0).mp (not_lt.mp hn)
      have hdK : K ^ (1 - ε) ≤ d := by
        rw [Real.rpow_sub hK0, Real.rpow_one, div_le_iff₀ (Real.rpow_pos_of_pos hK0 ε)]
        nlinarith [hhi]
      have hw : K ^ (2 - s) / (1 + d) ^ (3 - s) ≤ comparisonWeight N K s b ε i := by
        unfold comparisonWeight
        rw [ite_eq_left hdK]
        exact le_add_of_nonneg_left (by split_ifs <;> positivity)
      have hc : 1 + d ≤ 2 * K ^ ε * δ := by
        have hδ1 : 1 ≤ δ := hK.trans hδK
        have : 1 ≤ K ^ ε * δ := one_le_mul_of_one_le_of_one_le he hδ1
        linarith
      have hh := varAlSingular_inverse_power hK hε hd (lt_of_lt_of_le hK0 hδK)
        (by linarith : 0 ≤ 3 - s) (by linarith : 3 - s ≤ 3) hc
      have heq : K⁻¹ * (δ / K) ^ (s - 3) = K ^ (2 - s) * δ ^ (-(3 - s)) := by
        rw [Real.div_rpow hδ hK0.le, div_eq_mul_inv, ← Real.rpow_neg hK0.le,
          ← Real.rpow_neg_one, mul_left_comm, ← Real.rpow_add hK0]
        rw [show -1 + -(s - 3) = 2 - s by ring,
          show s - 3 = -(3 - s) by ring]
        ring
      rw [heq]
      calc K ^ (2 - s) * δ ^ (-(3 - s)) ≤
          K ^ (2 - s) * (8 * K ^ (3 * ε) / (1 + d) ^ (3 - s)) :=
            mul_le_mul_of_nonneg_left hh (by positivity)
        _ = 8 * K ^ (3 * ε) * (K ^ (2 - s) / (1 + d) ^ (3 - s)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hw (by positivity)
  exact (add_le_add hmain hlast).trans_eq (by unfold augmentedComparisonWeight; ring)

end Riesz1

end
