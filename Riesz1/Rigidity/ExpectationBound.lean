/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.ExpectationBoundError
public import Riesz1.ToMathlib.LogConcave.LinearTail

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
  obtain ⟨A, hA, he⟩ := expectation_error_cauchy_schwarz_internal
  let δ := 1 - (2 : ℝ) ^ (-γ)
  have hδ : 0 < δ :=
    sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))
  obtain ⟨K, hK, hb⟩ := exists_scale_exp_bound (c := blockMomentExponent / 2)
    (div_pos blockMomentExponent_pos (by norm_num)) hγ
  let C := max (δ⁻¹ * (A * K)) ((Real.exp (-2 * P.val.1) / 2)⁻¹ + 1)
  refine ⟨C, lt_of_lt_of_le (mul_pos (inv_pos.mpr hδ) (mul_pos hA hK)) (le_max_left _ _), ?_⟩
  intro hPL N hN θ hθ i j L k hL _hLN hij hk hjk
  let := isProbabilityMeasure_gibbsMeasure P N
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hR : 0 < (L : ℝ) ^ (1 + γ) := Real.rpow_pos_of_pos hLr _
  refine ⟨(blockLength_constrained_integral P N hθ i L hR j k).1, ?_⟩
  have hkL : k ≤ L := by omega
  by_cases hL1 : L = 1
  · have hk1 : k = 1 := by omega
    subst L
    subst k
    simp only [Nat.cast_one, Real.one_rpow]
    have hz := constrainedNormalizer_ge_one_gap P N hN hθ i
    have hinv : (constrainedNormalizer P N θ i 1 1)⁻¹ ≤ (Real.exp (-2 * P.val.1) / 2)⁻¹ :=
      inv_anti₀ (by positivity) hz
    have hmean := blockLength_constrained_integral P N hθ i 1 (by norm_num : (0 : ℝ) < 1) j 1
    have hpos (X : Configuration N) : 0 ≤ blockLength X j 1 := (blockLength_pos X j one_pos).le
    have hw : Integrable (fun X : Configuration N => blockLength X j 1 *
        Real.exp (-P.val.1 * forcingPotential θ i 1 1 X)) (gibbsMeasure P N) := by
      apply (integrable_blockLength P N j 1).mono'
        (((measurable_blockLength j 1).mul
          ((measurable_const.mul (measurable_forcingPotential hθ i 1 1)).exp)).aestronglyMeasurable)
      exact ae_of_all _ fun X => by
        change ‖blockLength X j 1 * Real.exp (-P.val.1 * forcingPotential θ i 1 1 X)‖ ≤ blockLength X j 1
        rw [Real.norm_of_nonneg (mul_nonneg (hpos X) (Real.exp_pos _).le)]
        exact mul_le_of_le_one_right (hpos X)
          (exp_neg_forcingPotential_le_one P hθ (by norm_num) N i 1 X)
    have hweighted : (∫ X : Configuration N, blockLength X j 1 *
        Real.exp (-P.val.1 * forcingPotential θ i 1 1 X) ∂gibbsMeasure P N) ≤ 1 := by
      have hh := integral_mono hw (integrable_blockLength P N j 1) fun X =>
        mul_le_of_le_one_right (hpos X)
          (exp_neg_forcingPotential_le_one P hθ (by norm_num) N i 1 X)
      simpa only [integral_blockLength_gibbsMeasure P N hN, Nat.cast_one] using hh
    have hzpos := (constrainedNormalizer_mem_Ioc P N hθ (by norm_num : (0 : ℝ) < 1) i 1).1
    have hupper : (∫ X : Configuration N, blockLength X j 1 ∂constrainedLaw P N θ i 1 1) ≤
        (Real.exp (-2 * P.val.1) / 2)⁻¹ := by
      rw [hmean.2]
      exact (mul_le_of_le_one_right (inv_nonneg.mpr hzpos.le) hweighted).trans hinv
    have hlower : 0 ≤ ∫ X : Configuration N, blockLength X j 1 ∂constrainedLaw P N θ i 1 1 :=
      integral_nonneg hpos
    exact (abs_le.mpr ⟨by linarith, by linarith⟩ :
      |(∫ X : Configuration N, blockLength X j 1 ∂constrainedLaw P N θ i 1 1) - 1| ≤
        (Real.exp (-2 * P.val.1) / 2)⁻¹ + 1).trans (le_max_right _ _)
  · have hz := constrainedNormalizer_ge_two P N hN hθ i (by omega : 2 ≤ L) hγ
    have hinv : (constrainedNormalizer P N θ i L ((L : ℝ) ^ (1 + γ)))⁻¹ ≤ δ⁻¹ :=
      inv_anti₀ hδ hz
    have herr := he hPL P N hN θ hθ i j L k hL hk _ hR
    have hratio : (L : ℝ) ^ (1 + γ) / (L : ℝ) = (L : ℝ) ^ γ := by
      rw [Real.rpow_add hLr, Real.rpow_one, mul_div_cancel_left₀ _ hLr.ne']
    rw [hratio] at herr
    have hscale : (k : ℝ) * Real.exp (-blockMomentExponent * (L : ℝ) ^ γ / 2) ≤ K := by
      have heq : -blockMomentExponent * (L : ℝ) ^ γ / 2 = -(blockMomentExponent / 2) * (L : ℝ) ^ γ := by ring
      rw [heq]
      exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hkL) (Real.exp_pos _).le).trans
        (hb (L : ℝ) hLr)
    calc |(∫ X : Configuration N, blockLength X j k
          ∂constrainedLaw P N θ i L ((L : ℝ) ^ (1 + γ))) - (k : ℝ)| ≤
        (constrainedNormalizer P N θ i L ((L : ℝ) ^ (1 + γ)))⁻¹ *
          (A * (k : ℝ) * Real.exp (-blockMomentExponent * (L : ℝ) ^ γ / 2)) := herr
      _ ≤ δ⁻¹ * (A * (k : ℝ) * Real.exp (-blockMomentExponent * (L : ℝ) ^ γ / 2)) :=
        mul_le_mul_of_nonneg_right hinv (by positivity)
      _ = δ⁻¹ * (A * ((k : ℝ) * Real.exp (-blockMomentExponent * (L : ℝ) ^ γ / 2))) := by ring
      _ ≤ δ⁻¹ * (A * K) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hscale hA.le) (inv_nonneg.mpr hδ.le)
      _ ≤ C := le_max_left _ _

end Riesz1

end
