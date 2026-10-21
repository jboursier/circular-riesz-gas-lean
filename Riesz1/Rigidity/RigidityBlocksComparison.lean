/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.BlockAverage
public import Riesz1.Rigidity.BlockMoments
public import Riesz1.Rigidity.ForcingComparison

/-!
# The total variation error in block difference concentration

The exponential comparison step in the proof of Theorem 1, with its numerical exponent.
No concentration assumption on the observable is used.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

/-- Convexification at radius `L^(1+γ)` changes the actual Gibbs law by at
most `3 exp(-c₀ L^γ)`. The constant `c₀` is numerical. -/
theorem rigidityBlocks_totalVariation (hPL : External.PrekopaLeindler)
    (P : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) (i₀ : ℤ) {L : ℕ}
    (hL : 0 < L) (hLN : L < (N : ℕ)) (γ : ℝ) :
    totalVariation (gibbsMeasure P N)
        (constrainedLaw P N θ i₀ L ((L : ℝ) ^ (1 + γ))) ≤
      3 * Real.exp (-blockMomentExponent * (L : ℝ) ^ γ) := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hR : 0 < (L : ℝ) ^ (1 + γ) := Real.rpow_pos_of_pos hLr _
  have h := forcing_event_comparison P N θ hθ i₀ L hLN _ hR
  have ht := blockLength_upper_tail hPL P N hN i₀ L hL ((L : ℝ) ^ γ)
  have he : (L : ℝ) * (L : ℝ) ^ γ = (L : ℝ) ^ (1 + γ) := by
    rw [Real.rpow_add hLr, Real.rpow_one]
  rw [he] at ht
  exact (h.1.trans h.2.1).trans ht

/-- The comparison applies to the block-difference tail at every real
threshold. This form is ready to combine with a tail bound under `Q`. -/
theorem rigidityBlocks_tail_transfer (hPL : External.PrekopaLeindler)
    (P : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) (i₀ i : ℤ) {L : ℕ}
    (hL : 0 < L) (hLN : L < (N : ℕ)) (γ : ℝ) (k : ℕ) (v : ℝ) :
    (gibbsMeasure P N).real {X | v ≤ |centeredBlockDiff X i k|} ≤
      (constrainedLaw P N θ i₀ L ((L : ℝ) ^ (1 + γ))).real
          {X | v ≤ |centeredBlockDiff X i k|} +
        3 * Real.exp (-blockMomentExponent * (L : ℝ) ^ γ) := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  let := isProbabilityMeasure_gibbsMeasure P N
  let := isProbabilityMeasure_constrainedLaw P N hθ
    (Real.rpow_pos_of_pos hLr (1 + γ)) i₀ L
  have hm : MeasurableSet {X : Configuration N | v ≤ |centeredBlockDiff X i k|} :=
    measurableSet_le measurable_const (continuous_abs.measurable.comp (measurable_centeredBlockDiff i k))
  have he := abs_measureReal_sub_le_etvDist_div_two (gibbsMeasure P N)
    (constrainedLaw P N θ i₀ L ((L : ℝ) ^ (1 + γ))) hm
  have hb := rigidityBlocks_totalVariation hPL P N hN hθ i₀ hL hLN γ
  change |_ - _| ≤ totalVariation _ _ at he
  linarith [(le_abs_self (_ - _)).trans (he.trans hb)]

/-- In the local range, the error in equation (4.9) is
bounded by the desired final exponential scale. -/
theorem rigidityBlocks_local_totalVariation (hPL : External.PrekopaLeindler)
    (P : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) (i : ℤ) {k : ℕ}
    (hk : 1 ≤ k) (hkN : 3 * k < (N : ℕ)) {γ : ℝ} (hγ : 0 ≤ γ) :
    totalVariation (gibbsMeasure P N)
        (constrainedLaw P N θ (i - k) (3 * k) (((3 * k : ℕ) : ℝ) ^ (1 + γ))) ≤
      3 * Real.exp (-blockMomentExponent * (k : ℝ) ^ γ) := by
  have h := rigidityBlocks_totalVariation hPL P N hN hθ (i - k)
    (by omega : 0 < 3 * k) hkN γ
  refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num))
  have hp : (k : ℝ) ^ γ ≤ ((3 * k : ℕ) : ℝ) ^ γ :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast (show k ≤ 3 * k by omega)) hγ
  nlinarith [blockMomentExponent_pos]

end Riesz1

end
