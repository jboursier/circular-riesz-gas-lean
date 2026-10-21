/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriComparisonWeights
public import Riesz1.Variance.APrioriRotationTranslationLabels
public import Riesz1.Variance.APrioriRotationTranslationSum
public import Riesz1.ToMathlib.Calculus.RealPowerTail

/-!
# Summation bounds for the a priori comparator

Part of Lemma 5.2, both summation assertions. The
power loss is `K^(2ε)`, uniformly for `0 < ε ≤ 1`. No rigidity or external
analytic theorem is needed for these deterministic estimates.
-/

@[expose] public section

noncomputable section

open Finset

namespace Riesz1

namespace APrioriComparison

/-- Harmonic sum up to a real power of the microscopic scale. -/
theorem harmonic_power_le {K t ε : ℝ} (hK : 1 ≤ K) (ht : 0 ≤ t) (hε : 0 < ε) :
    ∑ j ∈ Icc 1 ⌊K ^ t⌋₊, (1 : ℝ) / j ≤ (1 + t / ε) * K ^ ε := by
  have hK0 : 0 < K := by linarith
  have hT : 1 ≤ K ^ t := Real.one_le_rpow hK ht
  have hM : 1 ≤ ⌊K ^ t⌋₊ := Nat.le_floor (by simpa using hT)
  have hM0 : (0 : ℝ) < (⌊K ^ t⌋₊ : ℕ) := by exact_mod_cast (by omega : 0 < ⌊K ^ t⌋₊)
  have hlog : Real.log (⌊K ^ t⌋₊ : ℕ) ≤ t * Real.log K := by
    calc Real.log (⌊K ^ t⌋₊ : ℕ) ≤ Real.log (K ^ t) :=
        Real.log_le_log hM0 (Nat.floor_le (by positivity))
      _ = t * Real.log K := Real.log_rpow hK0 _
  have hlK := Real.log_le_rpow_div hK0.le hε
  have hKe : 1 ≤ K ^ ε := Real.one_le_rpow hK hε.le
  have htlog := mul_le_mul_of_nonneg_left hlK ht
  have hh := sum_Icc_inv_le ⌊K ^ t⌋₊
  calc _ ≤ 1 + t * Real.log K := by linarith
    _ ≤ (1 + t / ε) * K ^ ε := by
      have heq : t * (K ^ ε / ε) = (t / ε) * K ^ ε := by ring
      rw [heq] at htlog
      nlinarith

/-- Pointwise reduction of the head of the weight to a harmonic term. -/
theorem head_term_le {K s lam ε d : ℝ} (hK : 1 ≤ K) (hs : 0 < s) (hs1 : s < 1)
    (hlam : 0 ≤ lam) (hε : 0 ≤ ε) (hd : 1 ≤ d) (hdK : d ≤ K ^ (1 + ε)) :
    K ^ lam / (1 + d) ^ (1 + lam) * d ^ (s / 2) ≤
      ((K ^ lam + K ^ (s / 2)) * K ^ ε) * (1 / d) := by
  have hK0 : 0 < K := by linarith
  have hd0 : 0 < d := by linarith
  have hden : d ^ (1 + lam) ≤ (1 + d) ^ (1 + lam) :=
    Real.rpow_le_rpow hd0.le (by linarith) (by linarith)
  have hfactor : K ^ lam * d ^ (s / 2 - lam) ≤ (K ^ lam + K ^ (s / 2)) * K ^ ε := by
    by_cases hq : s / 2 - lam ≤ 0
    · have hdq := Real.rpow_le_one_of_one_le_of_nonpos hd hq
      have hKe := Real.one_le_rpow hK hε
      nlinarith [Real.rpow_nonneg hK0.le lam, Real.rpow_nonneg hK0.le (s / 2)]
    · have hq0 : 0 ≤ s / 2 - lam := by linarith
      have hdp : d ^ (s / 2 - lam) ≤ K ^ ((1 + ε) * (s / 2 - lam)) := by
        rw [Real.rpow_mul hK0.le]
        exact Real.rpow_le_rpow hd0.le hdK hq0
      have he : lam + (1 + ε) * (s / 2 - lam) ≤ s / 2 + ε := by
        nlinarith
      have hpow : K ^ lam * K ^ ((1 + ε) * (s / 2 - lam)) ≤ K ^ (s / 2) * K ^ ε := by
        rw [← Real.rpow_add hK0, ← Real.rpow_add hK0]
        exact Real.rpow_le_rpow_of_exponent_le hK he
      have h := mul_le_mul_of_nonneg_left hdp (Real.rpow_nonneg hK0.le lam)
      have hnon : 0 ≤ K ^ lam * K ^ ε := by positivity
      nlinarith
  calc K ^ lam / (1 + d) ^ (1 + lam) * d ^ (s / 2)
      ≤ K ^ lam / d ^ (1 + lam) * d ^ (s / 2) :=
        mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_left (by positivity) (by positivity) hden) (by positivity)
    _ = (K ^ lam * d ^ (s / 2 - lam)) * (1 / d) := by
      rw [Real.rpow_sub hd0, Real.rpow_add hd0, Real.rpow_one]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hfactor (by positivity)

/-- Head sum over arbitrary natural distances. -/
theorem head_sum_le {K s lam ε : ℝ} (hK : 1 ≤ K) (hs : 0 < s) (hs1 : s < 1)
    (hlam : 0 ≤ lam) (hε : 0 < ε) (hε1 : ε ≤ 1) (S : Finset ℕ)
    (hS : ∀ d ∈ S, 1 ≤ d ∧ (d : ℝ) ≤ K ^ (1 + ε)) :
    ∑ d ∈ S, K ^ lam / (1 + (d : ℝ)) ^ (1 + lam) * (d : ℝ) ^ (s / 2) ≤
      (1 + 2 / ε) * K ^ (2 * ε) * (K ^ lam + K ^ (s / 2)) := by
  have hK0 : 0 < K := by linarith
  have hsub : S ⊆ Icc 1 ⌊K ^ (1 + ε)⌋₊ := by
    intro d hd
    exact mem_Icc.mpr ⟨(hS d hd).1, Nat.le_floor (hS d hd).2⟩
  have hh : ∑ d ∈ S, (1 : ℝ) / d ≤ (1 + 2 / ε) * K ^ ε := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)).trans
    apply (harmonic_power_le hK (show 0 ≤ 1 + ε by linarith) hε).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have hfrac : (1 + ε) / ε ≤ 2 / ε :=
      (div_le_div_iff_of_pos_right hε).mpr (by linarith)
    linarith
  calc _ ≤ ∑ d ∈ S, ((K ^ lam + K ^ (s / 2)) * K ^ ε) * (1 / (d : ℝ)) := by
        apply Finset.sum_le_sum
        intro d hd
        exact head_term_le hK hs hs1 hlam hε.le (by exact_mod_cast (hS d hd).1) (hS d hd).2
    _ = ((K ^ lam + K ^ (s / 2)) * K ^ ε) * ∑ d ∈ S, (1 / (d : ℝ)) := by
        rw [Finset.mul_sum]
    _ ≤ ((K ^ lam + K ^ (s / 2)) * K ^ ε) * ((1 + 2 / ε) * K ^ ε) :=
        mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by rw [show 2 * ε = ε + ε by ring, Real.rpow_add hK0]; ring

/-- Tail sum over arbitrary natural distances. -/
theorem tail_sum_le {K s ε : ℝ} (hK : 1 ≤ K) (hs : 0 < s) (hs1 : s < 1)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (S : Finset ℕ)
    (hS : ∀ d ∈ S, K ^ (1 - ε) ≤ (d : ℝ)) :
    ∑ d ∈ S, K ^ (2 - s) / (1 + (d : ℝ)) ^ (3 - s) * (d : ℝ) ^ (s / 2) ≤
      (1 + 1 / (2 - 3 * s / 2)) * K ^ (2 * ε) * K ^ (s / 2) := by
  have hK0 : 0 < K := by linarith
  have hR : 1 ≤ K ^ (1 - ε) := Real.one_le_rpow hK (by linarith)
  have hp : 1 < 3 - 3 * s / 2 := by linarith
  have hterm : ∀ d ∈ S,
      K ^ (2 - s) / (1 + (d : ℝ)) ^ (3 - s) * (d : ℝ) ^ (s / 2) ≤
        K ^ (2 - s) * (d : ℝ) ^ (-(3 - 3 * s / 2)) := by
    intro d hd
    have hd0 : 0 < (d : ℝ) := lt_of_lt_of_le (by linarith) (hR.trans (hS d hd))
    have hden : (d : ℝ) ^ (3 - s) ≤ (1 + (d : ℝ)) ^ (3 - s) :=
      Real.rpow_le_rpow hd0.le (by linarith) (by linarith)
    calc _ ≤ K ^ (2 - s) / (d : ℝ) ^ (3 - s) * (d : ℝ) ^ (s / 2) :=
          mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_left (by positivity) (by positivity) hden) (by positivity)
      _ = _ := by
          rw [show -(3 - 3 * s / 2) = s / 2 - (3 - s) by ring]
          conv_rhs => rw [Real.rpow_sub hd0]
          ring
  have ht := sum_natCast_rpow_neg_le_of_real_ge hp hR S hS
  calc _ ≤ ∑ d ∈ S, K ^ (2 - s) * (d : ℝ) ^ (-(3 - 3 * s / 2)) :=
        Finset.sum_le_sum hterm
    _ = K ^ (2 - s) * ∑ d ∈ S, (d : ℝ) ^ (-(3 - 3 * s / 2)) := by rw [Finset.mul_sum]
    _ ≤ K ^ (2 - s) * ((1 + 1 / ((3 - 3 * s / 2) - 1)) *
        (K ^ (1 - ε)) ^ (1 - (3 - 3 * s / 2))) :=
        mul_le_mul_of_nonneg_left ht (by positivity)
    _ = (1 + 1 / (2 - 3 * s / 2)) * K ^ (s / 2 + (2 - 3 * s / 2) * ε) := by
        rw [← Real.rpow_mul hK0.le]
        have he : (2 - s) + (1 - ε) * (1 - (3 - 3 * s / 2)) =
            s / 2 + (2 - 3 * s / 2) * ε := by ring
        rw [← mul_assoc, mul_comm (K ^ (2 - s)), mul_assoc, ← Real.rpow_add hK0, he]
        congr 2; ring
    _ ≤ _ := by
        rw [mul_assoc, ← Real.rpow_add hK0]
        apply mul_le_mul_of_nonneg_left _ (by
          have : 0 < 2 - 3 * s / 2 := by linarith
          positivity)
        apply Real.rpow_le_rpow_of_exponent_le hK
        nlinarith

end APrioriComparison

end Riesz1

end
