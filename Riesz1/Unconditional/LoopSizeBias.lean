/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopSizeBiasComplete
public import Riesz1.Auxiliary.LoopSizeBiasTails
public import Riesz1.Rigidity.RigidityTheorem

/-!
# The preceding-particle change of anchor, with the externals as hypotheses

Restatements of the conditional theorems
`Riesz1.Internal.loopSizeBiased_blockDeviation_of_rigidity`,
`loopSizeBiased_cutoff_probability_of_rigidity` and `loopSizeBiased_gap_tail_of_rigidity`. The
rigidity hypothesis is replaced by the externals `Riesz1.External.BakryEmery` and
`Riesz1.External.PrekopaLeindler`.

The theorem for the size-bias part of Lemma 5.8 is `auxiliary_Loop_size_bias_label`.
It is the conjunction of the unconditional joint law,
normalization, marginal and norm comparison (`Riesz1.auxiliary_Loop_size_bias`), the inverse
block moments (`Riesz1.loopSizeBiased_inverse_blocks`), and the three restated theorems.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Riesz1

/-- The block fluctuation moments under the size-biased law, with the externals as hypotheses. -/
theorem loopSizeBiased_blockDeviation (hBE : External.BakryEmery)
    (hPL : External.PrekopaLeindler) (β s : ℝ) (hβ : 0 < β) (hs : 0 < s) (hs1 : s < 1) :
    ∃ eps0 : ℝ, 0 < eps0 ∧ ∀ δ : ℝ, 0 < δ → δ < min (s / 2) eps0 → ∀ p : ℝ, 1 ≤ p →
      ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (i : Fin (((n + 1).succPNat : ℕ))) (k : ℕ),
        1 ≤ k → k ≤ (n + 2) / 2 →
        eLpNorm (fun y => loopAnchoredBlock n (i : ℕ) k y - k) (ENNReal.ofReal p)
          (loopSizeBiasedLaw ⟨(β, s), hβ, hs, hs1⟩ n) ≤
            ENNReal.ofReal (C * (k : ℝ) ^ (s / 2 + δ)) := by
  obtain ⟨eps0, heps0, h⟩ := Internal.loopSizeBiased_blockDeviation_of_rigidity β s hβ hs hs1
    (Internal.rigidityConclusion_of_externals hBE hPL β s hβ hs hs1)
  refine ⟨eps0, heps0, fun δ hδ hδs p hp => ?_⟩
  obtain ⟨C, hC, h'⟩ := h δ hδ hδs p hp
  exact ⟨C, hC, h' hPL⟩

/-- The nearest-particle cutoff probability under the size-biased law, for every inverse power
`B₀`, with the externals as hypotheses. -/
theorem loopSizeBiased_cutoff_probability (hBE : External.BakryEmery)
    (hPL : External.PrekopaLeindler) (β s : ℝ) (hβ : 0 < β) (hs : 0 < s) (hs1 : s < 1)
    (γ ε : ℝ) (hγ : 1 < γ) (hε : 0 < ε) (hε1 : ε < min (1 / 8) ((1 - s / 2) / 8))
    {B₀ : ℝ} (hB₀ : 0 < B₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (ℓ : ℝ), 0 < ℓ → ℓ ≤ 1 → 1 ≤ (n + 2 : ℕ) * ℓ →
      loopSizeBiasedLaw ⟨(β, s), hβ, hs, hs1⟩ n
        {y | loopCutoff s γ ε (n + 1).succPNat ℓ (anchorVector y) ≠ 1} ≤
          ENNReal.ofReal (C * (((n + 2 : ℕ) : ℝ) * ℓ) ^ (-B₀)) :=
  Internal.loopSizeBiased_cutoff_probability_of_rigidity β s hβ hs hs1
    (Internal.rigidityConclusion_of_externals hBE hPL β s hβ hs hs1) hPL γ ε hγ hε hε1 hB₀

/-- The stretched exponential gap tails under the size-biased law, with the externals as
hypotheses. -/
theorem loopSizeBiased_gap_tail (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (β s : ℝ) (hβ : 0 < β) (hs : 0 < s) (hs1 : s < 1) :
    ∃ eps0 : ℝ, 0 < eps0 ∧ ∀ δ : ℝ, 0 < δ → δ < eps0 →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (n : ℕ) (i : Fin (((n + 1).succPNat : ℕ))) (k : ℕ),
        1 ≤ k → k ≤ (n + 2) / 2 →
        loopSizeBiasedLaw ⟨(β, s), hβ, hs, hs1⟩ n
          {y | |loopAnchoredBlock n (i : ℕ) k y - k| ≥ (k : ℝ) ^ (s / 2 + δ)} ≤
            ENNReal.ofReal (C * Real.exp (-c * (k : ℝ) ^ (δ / (4 * (s + 2))))) := by
  obtain ⟨eps0, heps0, h⟩ := Internal.loopSizeBiased_gap_tail_of_rigidity β s hβ hs hs1
    (Internal.rigidityConclusion_of_externals hBE hPL β s hβ hs hs1)
  refine ⟨eps0, heps0, fun δ hδ hδs => ?_⟩
  obtain ⟨c, C, hc, hC, h'⟩ := h δ hδ hδs
  exact ⟨c, C, hc, hC, h' hPL⟩

/-- The size-bias part of Lemma 5.8, with the externals as hypotheses. It states the
change of anchor (joint law, normalization, marginal and the `L^p`
comparison), the inverse block moments, the block fluctuation moments, the cutoff probabilities
of every inverse power, and the stretched exponential gap tails, all under the size-biased law. -/
theorem auxiliary_Loop_size_bias_label (hBE : External.BakryEmery)
    (hPL : External.PrekopaLeindler) (β s : ℝ) (hβ : 0 < β) (hs : 0 < s) (hs1 : s < 1)
    (γ ε : ℝ) (hγ : 1 < γ) (hε : 0 < ε) (hε1 : ε < min (1 / 8) ((1 - s / 2) / 8)) :
    (∀ n : ℕ,
      ((loopPrecedingMeasure ⟨(β, s), hβ, hs, hs1⟩ (n + 1).succPNat).map
        (fun X => (loopPrecedingOffsets X, loopPrecedingD X)) =
        ((anchoredLaw ⟨(β, s), hβ, hs, hs1⟩ (n + 1)).prod (volume : Measure ℝ)).restrict
          {p | 0 < p.2 ∧ p.2 < loopSizeWeight n p.1}) ∧
      (∫ y, loopSizeWeight n y ∂anchoredLaw ⟨(β, s), hβ, hs, hs1⟩ (n + 1) = 1) ∧
      ((loopPrecedingMeasure ⟨(β, s), hβ, hs, hs1⟩ (n + 1).succPNat).map loopPrecedingOffsets =
        loopSizeBiasedLaw ⟨(β, s), hβ, hs, hs1⟩ n) ∧
      (∀ (T : (Fin (n + 1) → ℝ) → ℝ) (p : ℝ), Measurable T → 1 ≤ p →
        eLpNorm T (ENNReal.ofReal p) (loopSizeBiasedLaw ⟨(β, s), hβ, hs, hs1⟩ n) ≤
          eLpNorm (loopSizeWeight n) 2 (anchoredLaw ⟨(β, s), hβ, hs, hs1⟩ (n + 1)) ^ (1 / p) *
            eLpNorm T (ENNReal.ofReal (2 * p)) (anchoredLaw ⟨(β, s), hβ, hs, hs1⟩ (n + 1)))) ∧
    (∀ p : ℝ, 0 < p → ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (j : ℤ) (k : ℕ), 0 < k →
      (∫⁻ y, ENNReal.ofReal (loopAnchoredBlock n j k y ^ (-p))
          ∂loopSizeBiasedLaw ⟨(β, s), hβ, hs, hs1⟩ n) ≤
        ENNReal.ofReal (C * (k : ℝ) ^ (-p))) ∧
    (∃ eps0 : ℝ, 0 < eps0 ∧ ∀ δ : ℝ, 0 < δ → δ < min (s / 2) eps0 → ∀ p : ℝ, 1 ≤ p →
      ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (i : Fin (((n + 1).succPNat : ℕ))) (k : ℕ),
        1 ≤ k → k ≤ (n + 2) / 2 →
        eLpNorm (fun y => loopAnchoredBlock n (i : ℕ) k y - k) (ENNReal.ofReal p)
          (loopSizeBiasedLaw ⟨(β, s), hβ, hs, hs1⟩ n) ≤
            ENNReal.ofReal (C * (k : ℝ) ^ (s / 2 + δ))) ∧
    (∀ B₀ : ℝ, 0 < B₀ → ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (ℓ : ℝ), 0 < ℓ → ℓ ≤ 1 →
      1 ≤ (n + 2 : ℕ) * ℓ →
      loopSizeBiasedLaw ⟨(β, s), hβ, hs, hs1⟩ n
        {y | loopCutoff s γ ε (n + 1).succPNat ℓ (anchorVector y) ≠ 1} ≤
          ENNReal.ofReal (C * (((n + 2 : ℕ) : ℝ) * ℓ) ^ (-B₀))) ∧
    (∃ eps0 : ℝ, 0 < eps0 ∧ ∀ δ : ℝ, 0 < δ → δ < eps0 →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (n : ℕ) (i : Fin (((n + 1).succPNat : ℕ))) (k : ℕ),
        1 ≤ k → k ≤ (n + 2) / 2 →
        loopSizeBiasedLaw ⟨(β, s), hβ, hs, hs1⟩ n
          {y | |loopAnchoredBlock n (i : ℕ) k y - k| ≥ (k : ℝ) ^ (s / 2 + δ)} ≤
            ENNReal.ofReal (C * Real.exp (-c * (k : ℝ) ^ (δ / (4 * (s + 2)))))) := by
  refine ⟨fun n => auxiliary_Loop_size_bias ⟨(β, s), hβ, hs, hs1⟩ n, fun p hp => ?_,
    loopSizeBiased_blockDeviation hBE hPL β s hβ hs hs1,
    fun B₀ hB₀ => loopSizeBiased_cutoff_probability hBE hPL β s hβ hs hs1 γ ε hγ hε hε1 hB₀,
    loopSizeBiased_gap_tail hBE hPL β s hβ hs hs1⟩
  obtain ⟨C, hC, h⟩ := loopSizeBiased_inverse_blocks ⟨(β, s), hβ, hs, hs1⟩ hp
  exact ⟨C, hC, h hPL⟩

end Riesz1

end
end
