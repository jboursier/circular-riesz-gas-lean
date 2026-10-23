/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopMomentsCount
public import Riesz1.Auxiliary.LoopMomentsRooted
public import Riesz1.Auxiliary.LoopMomentsNear
public import Riesz1.Auxiliary.LoopMomentsDiscrepancy
public import Riesz1.Auxiliary.LoopMomentsBlocks

/-!
# Counts, discrepancies and rooted moments of microscopic arcs

The moments part of Lemma B.2, all claims, conditionally on the rigidity conclusion
`Riesz1.Internal.RigidityConclusion` (see Theorem 1). The claims are:

* counts: `‖M_J‖_{L^p} ≤ C(1 + r)` for every arc of length `r ≤ N`.
* rooted energies: `‖E_i‖_{L^p} ≤ C`.
* short arcs: `‖∑_{z_i ∈ J} E_i‖_{L^p} ≤ C` for `r ≤ 3`.
* discrepancies: `‖ν(J)‖_{L^p} ≤ C r^{s/2+δ}` for `1 ≤ r ≤ N/2`.
* block deviations: `‖S_{i,k} - k‖_{L^p} ≤ C k^{s/2+δ}` for `1 ≤ k ≤ N/2`.

The discrepancy and block deviation claims share one threshold `ε0`, the minimum of the two
thresholds they are proved with. Both bounds hold for every `δ < min(s/2, ε0)`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

attribute [local instance] Classical.propDecidable

namespace Riesz1

namespace Internal

/-- **Counts, discrepancies and rooted moments**, the moments part of Lemma B.2.
Conditionally on the rigidity conclusion at `beta, s`. Each constant depends only on the model
parameters, the exponent `p` and, for the last two claims, `δ`. It does not depend on `N`, the
label `i`, the arc `J`, or `hPL`. -/
theorem auxiliary_Loop_moments_of_rigidity (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1)
    (hRig : Internal.RigidityConclusion beta s hbeta hs hs1) :
    (∀ p : ℝ, 1 ≤ p → ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (N : ℕ+),
        2 ≤ (N : ℕ) → ∀ (a r : ℝ), 0 < r → r ≤ N →
          eLpNorm (fun X : Configuration N => loopCount a r X) (ENNReal.ofReal p)
            (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) ≤
            ENNReal.ofReal (C * (1 + r))) ∧
    (∀ p : ℝ, 1 ≤ p → ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (N : ℕ+)
        (i : Fin (N : ℕ)),
        eLpNorm (fun X : Configuration N => rootedEnergy s X i) (ENNReal.ofReal p)
          (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) ≤ ENNReal.ofReal C) ∧
    (∀ p : ℝ, 1 ≤ p → ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (N : ℕ+),
        2 ≤ (N : ℕ) → ∀ (a r : ℝ), 0 < r → r ≤ 3 → r ≤ N →
          eLpNorm (fun X : Configuration N => ∑ i : Fin (N : ℕ),
            if loopPos X i ∈ microArc N a r then rootedEnergy s X i else 0) (ENNReal.ofReal p)
            (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) ≤ ENNReal.ofReal C) ∧
    (∃ eps0 : ℝ, 0 < eps0 ∧ ∀ δ : ℝ, 0 < δ → δ < min (s / 2) eps0 → ∀ p : ℝ, 1 ≤ p →
      (∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (N : ℕ+), 2 ≤ (N : ℕ) →
        ∀ (a r : ℝ), 1 ≤ r → r ≤ (N : ℝ) / 2 →
          eLpNorm (fun X : Configuration N => loopDiscrepancy a r X) (ENNReal.ofReal p)
            (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) ≤
            ENNReal.ofReal (C * r ^ (s / 2 + δ))) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (N : ℕ+), 2 ≤ (N : ℕ) →
        ∀ (i : Fin (N : ℕ)) (k : ℕ), 1 ≤ k → k ≤ (N : ℕ) / 2 →
          eLpNorm (fun X : Configuration N => blockLength X (i : ℕ) k - k) (ENNReal.ofReal p)
            (gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N) ≤
            ENNReal.ofReal (C * (k : ℝ) ^ (s / 2 + δ)))) := by
  refine ⟨fun p hp => loopCount_eLpNorm _ hp, fun p hp => rootedEnergy_eLpNorm _ hs hp,
    fun p hp => shortArc_rootedEnergy_eLpNorm _ hs hp, ?_⟩
  obtain ⟨eps1, heps1, hdisc⟩ := discrepancy_eLpNorm_of_rigidity beta s hbeta hs hs1 hRig
  obtain ⟨eps2, heps2, hblk⟩ := blockDeviation_eLpNorm_of_rigidity beta s hbeta hs hs1 hRig
  refine ⟨min eps1 eps2, lt_min heps1 heps2, fun δ hδ hδlt p hp => ⟨?_, ?_⟩⟩
  · exact hdisc δ hδ (lt_of_lt_of_le hδlt (by
      apply min_le_min_left; exact min_le_left _ _)) p hp
  · exact hblk δ hδ (lt_of_lt_of_le hδlt (by
      apply min_le_min_left; exact min_le_right _ _)) p hp

end Internal

end Riesz1

end
end
