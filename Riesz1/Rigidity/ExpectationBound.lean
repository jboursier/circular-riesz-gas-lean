/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.ExpectationBoundError

/-!
# Uniform expectations under convexification

This is Lemma 4.3, including the smallest block sizes and every
admissible cutoff. The result holds for every positive exponent `γ`.
-/

public section

noncomputable section

open MeasureTheory

namespace Riesz1

/-- **Expectations under convexification**, Lemma 4.3.
The constant is chosen before the cutoff, particle number and all block data.
The result is strengthened from `γ ∈ (0,1)` to `γ > 0`. -/
theorem expectation_under_convexification (P : Parameters) {γ : ℝ} (hγ : 0 < γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (N : ℕ+)
      (_hN : 2 ≤ (N : ℕ)) (θ : ℝ → ℝ), IsForcingCutoff θ →
      ∀ (i j : ℤ) (L k : ℕ), 0 < L → L < (N : ℕ) →
      i ≤ j → 0 < k → j + (k : ℤ) ≤ i + (L : ℤ) →
      ∃ _h : Integrable (fun X : Configuration N => blockLength X j k)
          (constrainedLaw P N θ i L ((L : ℝ) ^ (1 + γ))),
        |(∫ X : Configuration N, blockLength X j k
          ∂constrainedLaw P N θ i L ((L : ℝ) ^ (1 + γ))) - (k : ℝ)| ≤ C := by
  have hc := blockMomentExponent_pos
  let δ := min (1 - (2 : ℝ) ^ (-γ)) (Real.exp (-2 * P.val.1) / 2)
  have hδ : 0 < δ := lt_min
    (sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)))
    (by positivity)
  obtain ⟨K, hK, hb⟩ := exists_scale_exp_bound (c := blockMomentExponent / 2)
    (div_pos blockMomentExponent_pos (by norm_num)) hγ
  let C := δ⁻¹ * (3 * (2 / blockMomentExponent + 1) * K)
  refine ⟨C, mul_pos (inv_pos.mpr hδ) (by positivity), ?_⟩
  intro hPL N hN θ hθ i j L k hL _hLN hij _hk hjk
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hR : 0 < (L : ℝ) ^ (1 + γ) := Real.rpow_pos_of_pos hLr _
  refine ⟨(blockLength_constrained_integral P N hθ i L hR j k).1, ?_⟩
  have hz : δ ≤ constrainedNormalizer P N θ i L ((L : ℝ) ^ (1 + γ)) := by
    by_cases hL1 : L = 1
    · subst L
      simp only [Nat.cast_one, Real.one_rpow]
      exact (min_le_right _ _).trans (constrainedNormalizer_ge_one_gap P N hN hθ i)
    · exact (min_le_left _ _).trans (constrainedNormalizer_ge_two P N hN hθ i (by omega) hγ)
  have hinv : (constrainedNormalizer P N θ i L ((L : ℝ) ^ (1 + γ)))⁻¹ ≤ δ⁻¹ :=
    inv_anti₀ hδ hz
  have he := expectation_error_exp_internal hPL P N hN hθ i j L k hL hij hjk hR
  have hratio : (L : ℝ) ^ (1 + γ) / (L : ℝ) = (L : ℝ) ^ γ := by
    rw [Real.rpow_add hLr, Real.rpow_one, mul_div_cancel_left₀ _ hLr.ne']
  rw [hratio] at he
  have hscale : (L : ℝ) * Real.exp (-blockMomentExponent * (L : ℝ) ^ γ / 2) ≤ K := by
    have heq : -blockMomentExponent * (L : ℝ) ^ γ / 2 = -(blockMomentExponent / 2) * (L : ℝ) ^ γ := by ring
    rw [heq]
    exact hb (L : ℝ) hLr
  calc |(∫ X : Configuration N, blockLength X j k
        ∂constrainedLaw P N θ i L ((L : ℝ) ^ (1 + γ))) - (k : ℝ)| ≤
      (constrainedNormalizer P N θ i L ((L : ℝ) ^ (1 + γ)))⁻¹ *
        (3 * (L : ℝ) * (2 / blockMomentExponent + 1) *
          Real.exp (-blockMomentExponent * (L : ℝ) ^ γ / 2)) := he
    _ ≤ δ⁻¹ * (3 * (L : ℝ) * (2 / blockMomentExponent + 1) *
          Real.exp (-blockMomentExponent * (L : ℝ) ^ γ / 2)) :=
        mul_le_mul_of_nonneg_right hinv (by positivity)
    _ = δ⁻¹ * ((3 * (2 / blockMomentExponent + 1)) *
          ((L : ℝ) * Real.exp (-blockMomentExponent * (L : ℝ) ^ γ / 2))) := by ring
    _ ≤ C := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hscale (by positivity)) (inv_nonneg.mpr hδ.le)

end Riesz1

end
