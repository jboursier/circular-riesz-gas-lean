/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriUnanchoredLaw
public import Riesz1.ToMathlib.WeightedExponentialTail
public import Riesz1.ToMathlib.VarianceTransferOn

/-!
# The weighted gap tail in the unanchored a priori estimate

The exponential one-gap moment supplies the weighted tail required by
the size-biased variance transfer in the proof of Lemma 5.2.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1.Internal

/-- The weighted size-bias tail is uniformly exponentially small, for
every real threshold and every particle number at least two. -/
theorem sizeBiasWeight_tail_le (hPL : External.PrekopaLeindler)
    (P : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (u : ℝ) :
    ∫ y in {y | u < sizeBiasWeight N hN y}, sizeBiasWeight N hN y
        ∂rotAnchoredLaw P N ≤
      (6 / blockMomentExponent) * Real.exp (-blockMomentExponent * u / 2) := by
  have hw := measurable_sizeBiasWeight N hN
  have he : (∫ y in {y | u < sizeBiasWeight N hN y}, sizeBiasWeight N hN y
      ∂rotAnchoredLaw P N) =
      ∫ X in {X : Configuration N | u < gap X 0}, gap X 0 ∂gibbsMeasure P N := by
    rw [← integral_indicator (measurableSet_lt measurable_const hw)]
    unfold rotAnchoredLaw
    rw [integral_map (measurable_rotAnchorVec N).aemeasurable
      (hw.indicator (measurableSet_lt measurable_const hw)).aestronglyMeasurable]
    rw [← integral_indicator (measurableSet_lt measurable_const (measurable_gap 0))]
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, sizeBiasWeight_anchorVec]
  rw [he]
  simpa only [show (2 : ℝ) * 3 = 6 by norm_num] using
    weighted_tail_le_of_exp_moment (gibbsMeasure P N) (measurable_gap 0)
    (fun X => (gap_pos X 0).le) blockMomentExponent_pos
    (integrable_exp_gap P N 0 _) (integral_exp_gap_le hPL P N hN 0) u

/-- Any fixed polynomial multiplying the weighted gap tail at `K^δ`
is bounded uniformly in `N` and `K ≥ 1`. Constants precede the model,
the particle number and the scale. -/
theorem sizeBiasWeight_tail_polynomial (D δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler)
      (P : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (K : ℝ), 1 ≤ K →
      K ^ D * (∫ y in {y | K ^ δ < sizeBiasWeight N hN y}, sizeBiasWeight N hN y
        ∂rotAnchoredLaw P N) ≤ C := by
  have hc := blockMomentExponent_pos
  obtain ⟨C, hC, hb⟩ := rpow_mul_exp_neg_bounded (β := D) hδ
    (show 0 < blockMomentExponent / 2 by linarith [blockMomentExponent_pos])
  refine ⟨(6 / blockMomentExponent) * (C + 1), by positivity, ?_⟩
  intro hPL P N hN K hK
  have hkp : 0 ≤ K ^ D := Real.rpow_nonneg (by linarith) _
  have ht := mul_le_mul_of_nonneg_left (sizeBiasWeight_tail_le hPL P N hN (K ^ δ)) hkp
  have he : -blockMomentExponent * K ^ δ / 2 = -(blockMomentExponent / 2) * K ^ δ := by ring
  rw [he] at ht
  calc _ ≤ (6 / blockMomentExponent) *
        (K ^ D * Real.exp (-(blockMomentExponent / 2) * K ^ δ)) := by
          convert ht using 1
          ring
    _ ≤ (6 / blockMomentExponent) * C :=
      mul_le_mul_of_nonneg_left (hb K hK) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

end Riesz1.Internal

end
