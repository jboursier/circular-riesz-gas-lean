/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.ExpectationBoundNormalizer

/-!
# Block expectations under the constrained law

Integrability and the centered change-of-density identity for Lemma 4.3.
-/

public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

/-- Internal weighted integrability, followed by the actual expectation under convexification. -/
theorem blockLength_constrained_integral (P : Parameters) (N : ℕ+)
    {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) (i : ℤ) (L : ℕ) {R : ℝ} (hR : 0 < R)
    (j : ℤ) (k : ℕ) :
    Integrable (fun X : Configuration N => blockLength X j k) (constrainedLaw P N θ i L R) ∧
    (∫ X : Configuration N, blockLength X j k ∂constrainedLaw P N θ i L R) =
      (constrainedNormalizer P N θ i L R)⁻¹ *
        ∫ X : Configuration N, blockLength X j k *
          Real.exp (-P.val.1 * forcingPotential θ i L R X) ∂gibbsMeasure P N := by
  let := isProbabilityMeasure_gibbsMeasure P N
  have hz := (constrainedNormalizer_mem_Ioc P N hθ hR i L).1
  have hd : Measurable (fun X : Configuration N => ENNReal.ofReal
      ((constrainedNormalizer P N θ i L R)⁻¹ * Real.exp (-P.val.1 * forcingPotential θ i L R X))) :=
    (measurable_const.mul ((measurable_const.mul (measurable_forcingPotential hθ i L R)).exp)).ennreal_ofReal
  have hnn (X : Configuration N) : 0 ≤ (constrainedNormalizer P N θ i L R)⁻¹ *
      Real.exp (-P.val.1 * forcingPotential θ i L R X) := by positivity
  have hA (X : Configuration N) : 0 ≤ blockLength X j k := by
    rw [blockLength_eq_sum]
    exact Finset.sum_nonneg fun r _ => (gap_pos X _).le
  have hw : Integrable (fun X : Configuration N => blockLength X j k *
      Real.exp (-P.val.1 * forcingPotential θ i L R X)) (gibbsMeasure P N) := by
    apply (integrable_blockLength P N j k).mono' (((measurable_blockLength j k).mul
      ((measurable_const.mul (measurable_forcingPotential hθ i L R)).exp)).aestronglyMeasurable)
    exact ae_of_all _ fun X => by
      change ‖blockLength X j k * Real.exp (-P.val.1 * forcingPotential θ i L R X)‖ ≤ blockLength X j k
      rw [Real.norm_of_nonneg (mul_nonneg (hA X) (Real.exp_pos _).le)]
      exact mul_le_of_le_one_right (hA X) (exp_neg_forcingPotential_le_one P hθ hR N i L X)
  have hs : Integrable (fun X : Configuration N =>
      (ENNReal.ofReal ((constrainedNormalizer P N θ i L R)⁻¹ *
        Real.exp (-P.val.1 * forcingPotential θ i L R X))).toReal • blockLength X j k)
      (gibbsMeasure P N) := by
    simp only [ENNReal.toReal_ofReal (hnn _), smul_eq_mul]
    exact (hw.const_mul (constrainedNormalizer P N θ i L R)⁻¹).congr (ae_of_all _ fun X => by dsimp; ring)
  refine ⟨?_, ?_⟩
  · exact (integrable_withDensity_iff_integrable_smul' hd (ae_of_all _ fun _ =>
      ENNReal.ofReal_lt_top)).mpr hs
  · change (∫ X : Configuration N, blockLength X j k ∂(gibbsMeasure P N).withDensity _) = _
    rw [integral_withDensity_eq_integral_toReal_smul hd (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (hnn _), smul_eq_mul]
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun X => by ring

/-- Internal centered identity. Both real expectations have integrability certificates. -/
theorem blockLength_constrained_centered_internal (P : Parameters) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ)
    (i : ℤ) (L : ℕ) {R : ℝ} (hR : 0 < R) (j : ℤ) (k : ℕ) :
    let w := fun X : Configuration N => Real.exp (-P.val.1 * forcingPotential θ i L R X)
    Integrable (fun X => (blockLength X j k - (k : ℝ)) * (w X - 1)) (gibbsMeasure P N) ∧
    (∫ X : Configuration N, blockLength X j k ∂constrainedLaw P N θ i L R) - (k : ℝ) =
      (constrainedNormalizer P N θ i L R)⁻¹ *
        ∫ X : Configuration N, (blockLength X j k - (k : ℝ)) * (w X - 1) ∂gibbsMeasure P N := by
  let := isProbabilityMeasure_gibbsMeasure P N
  dsimp only
  let w := fun X : Configuration N => Real.exp (-P.val.1 * forcingPotential θ i L R X)
  have hw := integrable_exp_neg_forcingPotential P N hθ hR i L
  change Integrable w (gibbsMeasure P N) at hw
  have hA := integrable_blockLength P N j k
  have hAw : Integrable (fun X : Configuration N => blockLength X j k * w X) (gibbsMeasure P N) := by
    apply hA.mono' ((measurable_blockLength j k).mul ((measurable_const.mul (measurable_forcingPotential hθ i L R)).exp)).aestronglyMeasurable
    exact ae_of_all _ fun X => by
      have ha : 0 ≤ blockLength X j k := by
        rw [blockLength_eq_sum]; exact Finset.sum_nonneg fun r _ => (gap_pos X _).le
      change ‖blockLength X j k * Real.exp (-P.val.1 * forcingPotential θ i L R X)‖ ≤ blockLength X j k
      rw [Real.norm_of_nonneg (mul_nonneg ha (Real.exp_pos _).le)]
      exact mul_le_of_le_one_right ha (exp_neg_forcingPotential_le_one P hθ hR N i L X)
  have hkw : Integrable (fun X : Configuration N => (k : ℝ) * w X) (gibbsMeasure P N) := hw.const_mul _
  have hisub1 : Integrable (fun X : Configuration N => blockLength X j k * w X - (k : ℝ) * w X) (gibbsMeasure P N) := hAw.sub hkw
  have hisub2 : Integrable (fun X : Configuration N => blockLength X j k * w X - (k : ℝ) * w X - blockLength X j k) (gibbsMeasure P N) := hisub1.sub hA
  have he (X : Configuration N) : (blockLength X j k - (k : ℝ)) * (w X - 1) =
      blockLength X j k * w X - (k : ℝ) * w X - blockLength X j k + (k : ℝ) := by ring
  have hi := ((hAw.sub (hw.const_mul (k : ℝ))).sub hA).add (integrable_const (k : ℝ))
  refine ⟨hi.congr (ae_of_all _ fun X => (he X).symm), ?_⟩
  have hei : (∫ X : Configuration N, (blockLength X j k - (k : ℝ)) * (w X - 1) ∂gibbsMeasure P N) =
      (∫ X : Configuration N, blockLength X j k * w X ∂gibbsMeasure P N) -
        (k : ℝ) * constrainedNormalizer P N θ i L R := by
    simp_rw [he]
    rw [integral_add hisub2 (integrable_const (k : ℝ)),
      integral_sub hisub1 hA, integral_sub hAw hkw,
      integral_const_mul, integral_blockLength_gibbsMeasure P N hN, integral_const, probReal_univ,
      one_smul]
    dsimp only [constrainedNormalizer, w]
    ring
  rw [(blockLength_constrained_integral P N hθ i L hR j k).2, hei]
  have hz := (constrainedNormalizer_mem_Ioc P N hθ hR i L).1
  dsimp only [w]
  field_simp

end Riesz1

end
