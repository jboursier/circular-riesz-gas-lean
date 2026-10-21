/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopSizeBiasTails

/-!
# The preceding-particle change of anchor

The joint law, normalization, marginal, and norm comparison of the size-bias part of
Lemma 5.8. Its quantitative consequences are
`loopSizeBiased_inverse_blocks`, and the three theorems
`Internal.loopSizeBiased_blockDeviation_of_rigidity`,
`Internal.loopSizeBiased_cutoff_probability_of_rigidity`, and
`Internal.loopSizeBiased_gap_tail_of_rigidity`.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Riesz1

/-- The size-bias part of Lemma 5.8, the change-of-anchor law and its analytic
comparison. `N = n + 2` ranges over every particle number in the paper. -/
theorem auxiliary_Loop_size_bias (P : Parameters) (n : ℕ) :
    ((loopPrecedingMeasure P (n + 1).succPNat).map
      (fun X => (loopPrecedingOffsets X, loopPrecedingD X)) =
      ((anchoredLaw P (n + 1)).prod (volume : Measure ℝ)).restrict
        {p | 0 < p.2 ∧ p.2 < loopSizeWeight n p.1}) ∧
    (∫ y, loopSizeWeight n y ∂anchoredLaw P (n + 1) = 1) ∧
    ((loopPrecedingMeasure P (n + 1).succPNat).map loopPrecedingOffsets = loopSizeBiasedLaw P n) ∧
    (∀ (T : (Fin (n + 1) → ℝ) → ℝ) (p : ℝ), Measurable T → 1 ≤ p →
      eLpNorm T (ENNReal.ofReal p) (loopSizeBiasedLaw P n) ≤
        eLpNorm (loopSizeWeight n) 2 (anchoredLaw P (n + 1)) ^ (1 / p) *
          eLpNorm T (ENNReal.ofReal (2 * p)) (anchoredLaw P (n + 1))) := by
  exact ⟨map_loopPrecedingJoint P n, integral_loopSizeWeight P n, map_loopPrecedingOffsets P n,
    fun T p hT hp => loopSizeBiased_eLpNorm_le P n hT (by linarith)⟩

end Riesz1

end
