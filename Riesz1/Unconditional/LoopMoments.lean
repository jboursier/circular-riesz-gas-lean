/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopMoments
public import Riesz1.Auxiliary.LoopMomentsBlocks
public import Riesz1.Auxiliary.LoopMomentsDiscrepancy
public import Riesz1.Rigidity.RigidityTheorem

/-!
# Moments of loop counts, discrepancies and block deviations, with the externals as hypotheses

Restatements of the conditional theorems
`Riesz1.Internal.auxiliary_Loop_moments_of_rigidity`, `blockDeviation_eLpNorm_of_rigidity` and
`discrepancy_eLpNorm_of_rigidity`. The rigidity hypothesis is replaced by the externals
`Riesz1.External.BakryEmery` and `Riesz1.External.PrekopaLeindler`, which are explicit arguments.
The inner `∀ (_hPL : External.PrekopaLeindler)` binders of the conditional statements are
removed, since the external is now an argument.

These restatements cover the open-arc claims of the moments part of Lemma 5.8. The closed and
half-open arcs are treated in `Riesz1.auxiliary_Loop_moments_arcs`.
-/

public section

noncomputable section

open MeasureTheory Finset Set
open scoped ENNReal

attribute [local instance] Classical.propDecidable

namespace Riesz1

/-- The open-arc moment bounds of Lemma 5.8, with the externals as hypotheses. -/
theorem auxiliary_Loop_moments (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1) :
    (∀ p : ℝ, 1 ≤ p → ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+),
        2 ≤ (N : ℕ) → ∀ (a r : ℝ), 0 < r → r ≤ N →
          eLpNorm (fun X : Configuration N => loopCount a r X) (ENNReal.ofReal p)
            (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) ≤
            ENNReal.ofReal (C * (1 + r))) ∧
    (∀ p : ℝ, 1 ≤ p → ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (i : Fin (N : ℕ)),
        eLpNorm (fun X : Configuration N => rootedEnergy s X i) (ENNReal.ofReal p)
          (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) ≤ ENNReal.ofReal C) ∧
    (∀ p : ℝ, 1 ≤ p → ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+),
        2 ≤ (N : ℕ) → ∀ (a r : ℝ), 0 < r → r ≤ 3 → r ≤ N →
          eLpNorm (fun X : Configuration N => ∑ i : Fin (N : ℕ),
            if loopPos X i ∈ microArc N a r then rootedEnergy s X i else 0) (ENNReal.ofReal p)
            (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) ≤ ENNReal.ofReal C) ∧
    (∃ eps0 : ℝ, 0 < eps0 ∧ ∀ δ : ℝ, 0 < δ → δ < min (s / 2) eps0 → ∀ p : ℝ, 1 ≤ p →
      (∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) →
        ∀ (a r : ℝ), 1 ≤ r → r ≤ (N : ℝ) / 2 →
          eLpNorm (fun X : Configuration N => loopDiscrepancy a r X) (ENNReal.ofReal p)
            (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) ≤
            ENNReal.ofReal (C * r ^ (s / 2 + δ))) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) →
        ∀ (i : Fin (N : ℕ)) (k : ℕ), 1 ≤ k → k ≤ (N : ℕ) / 2 →
          eLpNorm (fun X : Configuration N => blockLength X (i : ℕ) k - k) (ENNReal.ofReal p)
            (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) ≤
            ENNReal.ofReal (C * (k : ℝ) ^ (s / 2 + δ)))) := by
  obtain ⟨hA, hB, hC, hD⟩ := Internal.auxiliary_Loop_moments_of_rigidity beta s hbeta hs hs1
    (Internal.rigidityConclusion_of_externals hBE hPL beta s hbeta hs hs1)
  refine ⟨fun p hp => ?_, fun p hp => ?_, fun p hp => ?_, ?_⟩
  · obtain ⟨C, hC', h⟩ := hA p hp
    exact ⟨C, hC', h hPL⟩
  · obtain ⟨C, hC', h⟩ := hB p hp
    exact ⟨C, hC', h hPL⟩
  · obtain ⟨C, hC', h⟩ := hC p hp
    exact ⟨C, hC', h hPL⟩
  · obtain ⟨eps0, heps0, h⟩ := hD
    refine ⟨eps0, heps0, fun δ hδ hδs p hp => ?_⟩
    obtain ⟨⟨C₁, hC₁, h₁⟩, ⟨C₂, hC₂, h₂⟩⟩ := h δ hδ hδs p hp
    exact ⟨⟨C₁, hC₁, h₁ hPL⟩, ⟨C₂, hC₂, h₂ hPL⟩⟩

/-- The `L^p` bound on the block deviation `S_{i,k} - k`, with the externals as hypotheses. -/
theorem blockDeviation_eLpNorm (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1) :
    ∃ eps0 : ℝ, 0 < eps0 ∧ ∀ δ : ℝ, 0 < δ → δ < min (s / 2) eps0 → ∀ p : ℝ, 1 ≤ p →
      ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) →
        ∀ (i : Fin (N : ℕ)) (k : ℕ), 1 ≤ k → k ≤ (N : ℕ) / 2 →
          eLpNorm (fun X : Configuration N => blockLength X (i : ℕ) k - k) (ENNReal.ofReal p)
            (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) ≤
            ENNReal.ofReal (C * (k : ℝ) ^ (s / 2 + δ)) := by
  obtain ⟨eps0, heps0, h⟩ := Internal.blockDeviation_eLpNorm_of_rigidity beta s hbeta hs hs1
    (Internal.rigidityConclusion_of_externals hBE hPL beta s hbeta hs hs1)
  refine ⟨eps0, heps0, fun δ hδ hδs p hp => ?_⟩
  obtain ⟨C, hC, h⟩ := h δ hδ hδs p hp
  exact ⟨C, hC, h hPL⟩

/-- The `L^p` bound on the loop discrepancy of an arc of length `r`, with the externals as
hypotheses. -/
theorem discrepancy_eLpNorm (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1) :
    ∃ eps0 : ℝ, 0 < eps0 ∧ ∀ δ : ℝ, 0 < δ → δ < min (s / 2) eps0 → ∀ p : ℝ, 1 ≤ p →
      ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) →
        ∀ (a r : ℝ), 1 ≤ r → r ≤ (N : ℝ) / 2 →
          eLpNorm (fun X : Configuration N => loopDiscrepancy a r X) (ENNReal.ofReal p)
            (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) ≤
            ENNReal.ofReal (C * r ^ (s / 2 + δ)) := by
  obtain ⟨eps0, heps0, h⟩ := Internal.discrepancy_eLpNorm_of_rigidity beta s hbeta hs hs1
    (Internal.rigidityConclusion_of_externals hBE hPL beta s hbeta hs hs1)
  refine ⟨eps0, heps0, fun δ hδ hδs p hp => ?_⟩
  obtain ⟨C, hC, h⟩ := h δ hδ hδs p hp
  exact ⟨C, hC, h hPL⟩

end Riesz1

end
end
