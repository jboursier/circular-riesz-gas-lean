/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriBoundThresholds
public import Riesz1.Variance.APrioriRotationTranslationLabels

/-!
# Spatial envelopes and label weights

The pointwise derivative estimate in the proof of Lemma 5.2.
The large-scale estimate retains both sharp indicators. Its constants
are explicit and independent of particle number and window size.
-/

public section

noncomputable section

namespace Riesz1.Internal

/-- Rescaling a reciprocal power using the lower position-label bound.
The factor two accounts for the shift from `d` to `1 + d`. -/
theorem a_priori_scaled_power {K ε d t p : ℝ} (hK : 0 < K)
    (hd : 1 ≤ d) (hp : 0 ≤ p) (hlow : K ^ (-ε) * d ≤ K * t) :
    K⁻¹ * (1 / t ^ p) ≤
      2 ^ p * K ^ (p * ε) * (K ^ (p - 1) / (1 + d) ^ p) := by
  have hd0 : 0 < 1 + d := by linarith
  let z := K ^ (-ε) * (1 + d) / K
  have hz : 0 < z := by dsimp [z]; positivity
  have hzt : z / 2 ≤ t := by
    have he : z / 2 = (K ^ (-ε) * (1 + d) / 2) / K := by dsimp [z]; ring
    rw [he, div_le_iff₀ hK]
    have : 0 ≤ K ^ (-ε) := Real.rpow_nonneg hK.le _
    nlinarith
  have ht : 0 < t := lt_of_lt_of_le (by positivity : 0 < z / 2) hzt
  have hb := rpow_neg_le_two_pow_mul hz hzt hp
  rw [Real.rpow_neg ht.le, ← one_div] at hb
  apply (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hK.le)).trans_eq
  dsimp [z]
  rw [Real.rpow_neg (by positivity), Real.div_rpow (by positivity) hK.le,
    Real.mul_rpow (by positivity) hd0.le, ← Real.rpow_mul hK.le,
    show -ε * p = -(p * ε) by ring, Real.rpow_neg hK.le,
    Real.rpow_sub hK, Real.rpow_one]
  field_simp

/-- At large scales the original two comparison weights dominate the
rescaled spatial envelope. All assumptions are scalar geometric facts.
This is an internal helper rather than a variance claim. -/
theorem a_priori_envelope_large {N : ℕ+} {s lam K ε t : ℝ}
    (hs : 0 < s) (hs1 : s < 1) (hlam : 0 ≤ lam) (hK : 1 ≤ K)
    (hε : 0 < ε) (hεs : ε ≤ (1 - s / 2) / 2) (hlarge : 4 ≤ K ^ ε)
    (i : Fin (N : ℕ)) (hd : 1 ≤ (labelDistToOne N i : ℝ))
    (hlow : K ^ (-ε) * (labelDistToOne N i : ℝ) ≤ K * t)
    (herr : |K * t - (labelDistToOne N i : ℝ)| ≤
      K ^ ε * (labelDistToOne N i : ℝ) ^ (s / 2)) :
    K⁻¹ * cutoffMajorant s lam K t ≤
      (2 ^ (1 + lam) + 2 ^ (3 - s)) * K ^ ((3 + lam) * ε) *
        comparisonWeight N K s lam ε i := by
  have hK0 : 0 < K := by linarith
  have hd0 : 0 < (labelDistToOne N i : ℝ) := by linarith
  have ht : 0 < t := by
    have : 0 < K ^ (-ε) * (labelDistToOne N i : ℝ) := by positivity
    have : 0 < K * t := lt_of_lt_of_le this hlow
    exact pos_of_mul_pos_right this hK0.le
  have ha (p : ℝ) (hp : 0 ≤ p) (hpa : p ≤ 3 + lam) :
      K⁻¹ * (1 / t ^ p) ≤
        2 ^ p * K ^ ((3 + lam) * ε) *
          (K ^ (p - 1) / (1 + (labelDistToOne N i : ℝ)) ^ p) := by
    apply (a_priori_scaled_power hK0 hd hp hlow).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.rpow_le_rpow_of_exponent_le hK (mul_le_mul_of_nonneg_right hpa hε.le)
  have hnear : K⁻¹ * majorantNear lam K t ≤
      2 ^ (1 + lam) * K ^ ((3 + lam) * ε) *
        (if (labelDistToOne N i : ℝ) ≤ K ^ (1 + ε) then
          K ^ lam / (1 + (labelDistToOne N i : ℝ)) ^ (1 + lam) else 0) := by
    unfold majorantNear
    by_cases hn : t ≤ 2
    · have hdi := a_priori_inner_threshold hs hs1 hK hε hεs hlarge hd0 herr hn
      rw [ite_eq_left hn, ite_eq_left hdi]
      have hb := ha (1 + lam) (by linarith) (by linarith)
      rw [show 1 + lam - 1 = lam by ring] at hb
      apply le_trans _ hb
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hK0.le)
      exact one_div_le_one_div_of_le (by positivity)
        (Real.rpow_le_rpow ht.le (le_max_left _ _) (by linarith))
    · rw [ite_eq_right hn, mul_zero]
      positivity
  have hfar : K⁻¹ * majorantFar s t ≤
      2 ^ (3 - s) * K ^ ((3 + lam) * ε) *
        (if K ^ (1 - ε) ≤ (labelDistToOne N i : ℝ) then
          K ^ (2 - s) / (1 + (labelDistToOne N i : ℝ)) ^ (3 - s) else 0) := by
    unfold majorantFar
    by_cases hf : 2 ≤ t
    · have hdi := a_priori_outer_threshold hs hs1 hK hε.le (by linarith) hd0.le herr hf
      rw [ite_eq_left hf, ite_eq_left hdi]
      have hb := ha (3 - s) (by linarith) (by linarith)
      simpa only [show 3 - s - 1 = 2 - s by ring] using hb
    · rw [ite_eq_right hf, mul_zero]
      positivity
  unfold cutoffMajorant comparisonWeight
  rw [mul_add]
  have hw1 : 0 ≤ (if (labelDistToOne N i : ℝ) ≤ K ^ (1 + ε) then
      K ^ lam / (1 + (labelDistToOne N i : ℝ)) ^ (1 + lam) else 0) := by positivity
  have hw2 : 0 ≤ (if K ^ (1 - ε) ≤ (labelDistToOne N i : ℝ) then
      K ^ (2 - s) / (1 + (labelDistToOne N i : ℝ)) ^ (3 - s) else 0) := by positivity
  have hc1 : 0 ≤ 2 ^ (1 + lam) * K ^ ((3 + lam) * ε) := by positivity
  have hc2 : 0 ≤ 2 ^ (3 - s) * K ^ ((3 + lam) * ε) := by positivity
  nlinarith only [hnear, hfar, mul_nonneg hw1 hc2, mul_nonneg hw2 hc1]

/-- On a bounded scale interval the extra comparator term alone
dominates the derivative envelope, uniformly in the particle number.
No position-label comparison is needed in this range. -/
theorem a_priori_envelope_bounded {N : ℕ+} {s lam K γ B t : ℝ}
    (hs : 0 < s) (hs1 : s < 1) (hlam : 0 ≤ lam) (hK : 1 ≤ K)
    (hγ : 0 ≤ γ) (hKB : K ≤ B) (i : Fin (N : ℕ))
    (hi : i ∈ window N K γ) (ε : ℝ) :
    K⁻¹ * cutoffMajorant s lam K t ≤
      (2 * (1 + 4 * B ^ γ) ^ (1 + s / 2)) *
        augmentedComparisonWeight N K s lam ε i := by
  have hK0 : 0 < K := by linarith
  have hB : 0 < B := lt_of_lt_of_le hK0 hKB
  have hd : 1 + (labelDistToOne N i : ℝ) ≤ 1 + 4 * B ^ γ := by
    have hd := labelDist_le_of_mem_window hK hi
    have hp := Real.rpow_le_rpow hK0.le hKB hγ
    linarith
  have hp : (1 + (labelDistToOne N i : ℝ)) ^ (1 + s / 2) ≤
      (1 + 4 * B ^ γ) ^ (1 + s / 2) :=
    Real.rpow_le_rpow (by positivity) hd (by linarith)
  have hraw : K⁻¹ * cutoffMajorant s lam K t ≤ 2 * K ^ lam := by
    have hn := majorantNear_le hK hlam t
    have hf := majorantFar_le_one (by linarith : s < 3) t
    have hp : K ^ (1 + lam) = K * K ^ lam := by rw [Real.rpow_add hK0, Real.rpow_one]
    have hKi : K⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hK
    have hKl : 1 ≤ K ^ lam := Real.one_le_rpow hK hlam
    calc
      _ ≤ K⁻¹ * (K ^ (1 + lam) + 1) :=
        mul_le_mul_of_nonneg_left (add_le_add hn hf) (inv_nonneg.mpr hK0.le)
      _ = K ^ lam + K⁻¹ := by rw [hp]; field_simp
      _ ≤ 2 * K ^ lam := by linarith
  have hw : K ^ lam / (1 + (labelDistToOne N i : ℝ)) ^ (1 + s / 2) ≤
      augmentedComparisonWeight N K s lam ε i := by
    unfold augmentedComparisonWeight
    exact le_add_of_nonneg_left (comparisonWeight_nonneg hK0.le i)
  apply hraw.trans
  calc
    _ ≤ (2 * (1 + 4 * B ^ γ) ^ (1 + s / 2)) *
        (K ^ lam / (1 + (labelDistToOne N i : ℝ)) ^ (1 + s / 2)) := by
      have hpos : 0 < (1 + (labelDistToOne N i : ℝ)) ^ (1 + s / 2) := by positivity
      have he : 2 * K ^ lam = (2 * (1 + (labelDistToOne N i : ℝ)) ^ (1 + s / 2)) *
          (K ^ lam / (1 + (labelDistToOne N i : ℝ)) ^ (1 + s / 2)) := by field_simp
      rw [he]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hp (by norm_num : 0 ≤ (2 : ℝ))) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left hw (by positivity)

/-- The augmented label comparator controls the spatial derivative
envelope at every scale. The constant is chosen before `N,K,i,t`.
The exponent `3 + λ` is independent of `ε`. -/
theorem a_priori_envelope (s lam γ ε : ℝ)
    (hs : 0 < s) (hs1 : s < 1) (hlam : 0 ≤ lam) (hγ : 0 ≤ γ)
    (hε : 0 < ε) (hεs : ε ≤ (1 - s / 2) / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (K : ℝ), 1 ≤ K →
      ∀ i : Fin (N : ℕ), i ∈ window N K γ →
      1 ≤ (labelDistToOne N i : ℝ) → ∀ t : ℝ,
      K ^ (-ε) * (labelDistToOne N i : ℝ) ≤ K * t →
      |K * t - (labelDistToOne N i : ℝ)| ≤
        K ^ ε * (labelDistToOne N i : ℝ) ^ (s / 2) →
      K⁻¹ * cutoffMajorant s lam K t ≤
        C * K ^ ((3 + lam) * ε) * augmentedComparisonWeight N K s lam ε i := by
  let A : ℝ := 2 ^ (1 + lam) + 2 ^ (3 - s)
  let D : ℝ := 2 * (1 + 4 * ((4 : ℝ) ^ ε⁻¹) ^ γ) ^ (1 + s / 2)
  have hA : 0 < A := by dsimp [A]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨A + D, by positivity, fun N K hK i hi hd t hlow herr => ?_⟩
  have hK0 : 0 < K := by linarith
  have hw : 0 ≤ augmentedComparisonWeight N K s lam ε i :=
    augmentedComparisonWeight_nonneg hK0.le i
  have hpow : 1 ≤ K ^ ((3 + lam) * ε) := Real.one_le_rpow hK (by positivity)
  by_cases hlarge : 4 ≤ K ^ ε
  · have hb := a_priori_envelope_large hs hs1 hlam hK hε hεs hlarge i hd hlow herr
    have hcmp : comparisonWeight N K s lam ε i ≤ augmentedComparisonWeight N K s lam ε i := by
      unfold augmentedComparisonWeight
      exact le_add_of_nonneg_right (by positivity)
    apply hb.trans
    have hAp : 0 ≤ A * K ^ ((3 + lam) * ε) := by positivity
    exact mul_le_mul (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hD.le) (by positivity))
      hcmp (comparisonWeight_nonneg hK0.le i) (by positivity)
  · have hKB : K ≤ (4 : ℝ) ^ ε⁻¹ :=
      (Real.le_rpow_inv_iff_of_pos hK0.le (by norm_num) hε).mpr (le_of_not_ge hlarge)
    have hb := a_priori_envelope_bounded (t := t) hs hs1 hlam hK hγ hKB i hi ε
    apply hb.trans
    apply mul_le_mul_of_nonneg_right _ hw
    calc
      D ≤ (A + D) * 1 := by linarith
      _ ≤ (A + D) * K ^ ((3 + lam) * ε) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)

end Riesz1.Internal

end
