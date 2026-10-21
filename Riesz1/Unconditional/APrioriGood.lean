/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriGoodComplete
public import Riesz1.Variance.APrioriGoodProbability
public import Riesz1.Rigidity.RigidityTheorem

/-!
# The a-priori good event, with the externals as hypotheses

Restatements of the conditional theorems
`Riesz1.Internal.aPrioriGood_of_rigidity`, `aPrioriGood_complete_of_rigidity` and
`goodCutoff_prob_le_of_rigidity`. The rigidity hypothesis is replaced by the externals
`Riesz1.External.BakryEmery` and `Riesz1.External.PrekopaLeindler`, and the inner
`∀ (_hPL : External.PrekopaLeindler)` binders are removed.

The theorem for Lemma 5.2 is `aPrioriGood_complete`. It states every claim of that lemma,
namely the probability bound, the packing, the comparison and interval bounds on the good
event, the support, and the gradient bounds.
-/

public section

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal

namespace Riesz1

/-- The probability bound `P(η ≠ 1) ≤ C K^{-B}` for the a-priori cutoff, with the externals as
hypotheses. -/
theorem goodCutoff_prob_le (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1)
    (γ ε : ℝ) (hγ : 1 < γ) (hε : 0 < ε) (B : ℝ) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) →
      ∀ K : ℝ, 1 ≤ K → K ≤ (N : ℕ) →
        gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N
            {X | goodCutoff N s K γ ε X ≠ 1} ≤
          ENNReal.ofReal (C * K ^ (-B)) := by
  obtain ⟨C, hC, h⟩ := Internal.goodCutoff_prob_le_of_rigidity beta s hbeta hs hs1
    (Internal.rigidityConclusion_of_externals hBE hPL beta s hbeta hs hs1) γ ε hγ hε B hB
  exact ⟨C, hC, h hPL⟩

/-- The a-priori good event, with the deterministic and gradient claims and the probability
bound, with the externals as hypotheses. -/
theorem aPrioriGood (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1) (γ : ℝ) (hγ : 1 < γ) :
    (∀ ε : ℝ, 0 < ε → ∀ B : ℝ, 0 < B →
      ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) →
        ∀ K : ℝ, 1 ≤ K → K ≤ (N : ℕ) →
          gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N
              {X | goodCutoff N s K γ ε X ≠ 1} ≤
            ENNReal.ofReal (C * K ^ (-B))) ∧
    (∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ (N : ℕ+) (K : ℝ), 1 ≤ K →
      ∀ X : Configuration N, X ∈ goodEvent N s K γ ε →
        (∀ i j : Fin (N : ℕ), i ∈ window N K γ → j ∈ window N K γ →
          K ^ (-ε) * (cyclicIndexDistance N i j : ℝ)
              ≤ ((N : ℕ) : ℝ) * circDist 1 (X.val j - X.val i) ∧
            ((N : ℕ) : ℝ) * circDist 1 (X.val j - X.val i)
              ≤ 2 * K ^ ε * (cyclicIndexDistance N i j : ℝ)) ∧
        (∀ t₀ : ℝ, ((({i : Fin (N : ℕ) | i ∈ window N K γ ∧
            ∃ q : ℤ, X.val i + q ∈ Set.Ico t₀ (t₀ + 1 / ((N : ℕ) : ℝ))}).ncard : ℕ) : ℝ)
              ≤ 3 * K ^ ε) ∧
        (∀ i : Fin (N : ℕ), i ∈ window N K γ →
          |((N : ℕ) : ℝ) * (X.val i - X.val ⟨0, N.pos⟩) - ((i : ℕ) : ℝ)|
            ≤ K ^ ε * ((labelDistToOne N i : ℕ) : ℝ) ^ (s / 2))) ∧
    (∀ (N : ℕ+) (ε K : ℝ), 0 < K → ∀ X : Configuration N,
      goodCutoff N s K γ ε X ≠ 0 → X ∈ goodEvent N s K γ ε) ∧
    (∀ (N : ℕ+) (ε : ℝ), 0 ≤ ε → ∀ K : ℝ, 1 ≤ K →
      (∀ z : Fin (N : ℕ) → ℝ, gapCutoff N s K γ ε z = 1 →
        fderiv ℝ (gapCutoff N s K γ ε) z = 0) ∧
      (∀ z : Fin (N : ℕ) → ℝ, (∀ i : Fin (N : ℕ), 0 < z i) → z ∉ gapGoodEvent N s K γ ε →
        fderiv ℝ (gapCutoff N s K γ ε) z = 0) ∧
      (∀ i : Fin (N : ℕ), ∀ᵐ z ∂(volume : Measure (Fin (N : ℕ) → ℝ)),
        |fderiv ℝ (gapCutoff N s K γ ε) z (Pi.single i (1 : ℝ))| ≤ 76 * K ^ (2 * γ + ε))) ∧
    (∀ (N : ℕ+) (ε K : ℝ) (X : Configuration N),
      goodCutoff N s K γ ε X =
        gapCutoff N s K γ ε (fun i : Fin (N : ℕ) => gap X ((i : ℕ) : ℤ))) := by
  obtain ⟨hprob, hcomp, hsupp, hgrad, hbridge⟩ := Internal.aPrioriGood_of_rigidity beta s hbeta hs
    hs1 (Internal.rigidityConclusion_of_externals hBE hPL beta s hbeta hs hs1) γ hγ
  refine ⟨fun ε hε B hB => ?_, hcomp, hsupp, hgrad, hbridge⟩
  obtain ⟨C, hC, h⟩ := hprob ε hε B hB
  exact ⟨C, hC, h hPL⟩

/-- Lemma 5.2, with the externals as hypotheses. It states the probability bound
`P(η ≠ 1) ≤ C_B K^{-B}`, the two-sided comparison of
the selected labels, the packing bound, the anchored position bound, the support of the cutoff,
and the vanishing and Euclidean gradient bound `|∇η̃| ≤ C K^A` almost everywhere, together with
the identification of the cutoff with the gap cutoff. -/
theorem aPrioriGood_complete (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1) (γ : ℝ) (hγ : 1 < γ) :
    (∀ ε : ℝ, 0 < ε → ∀ B : ℝ, 0 < B →
      ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) →
        ∀ K : ℝ, 1 ≤ K → K ≤ (N : ℕ) →
          gibbsMeasure (⟨(beta, s), hbeta, hs, hs1⟩ : Parameters) N
              {X | goodCutoff N s K γ ε X ≠ 1} ≤
            ENNReal.ofReal (C * K ^ (-B))) ∧
    (∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ (N : ℕ+) (K : ℝ), 1 ≤ K →
      ∀ X : Configuration N, X ∈ goodEvent N s K γ ε →
        (∀ i j : Fin (N : ℕ), i ∈ window N K γ → j ∈ window N K γ →
          K ^ (-ε) * (cyclicIndexDistance N i j : ℝ)
              ≤ ((N : ℕ) : ℝ) * circDist 1 (X.val j - X.val i) ∧
            ((N : ℕ) : ℝ) * circDist 1 (X.val j - X.val i)
              ≤ 2 * K ^ ε * (cyclicIndexDistance N i j : ℝ)) ∧
        (∀ t₀ : ℝ, ((({i : Fin (N : ℕ) | i ∈ window N K γ ∧
            ∃ q : ℤ, X.val i + q ∈ Set.Ico t₀ (t₀ + 1 / ((N : ℕ) : ℝ))}).ncard : ℕ) : ℝ)
              ≤ 3 * K ^ ε) ∧
        (∀ i : Fin (N : ℕ), i ∈ window N K γ →
          |((N : ℕ) : ℝ) * (X.val i - X.val ⟨0, N.pos⟩) - ((i : ℕ) : ℝ)|
            ≤ K ^ ε * ((labelDistToOne N i : ℕ) : ℝ) ^ (s / 2))) ∧
    (∀ (N : ℕ+) (ε K : ℝ), 0 < K → ∀ X : Configuration N,
      goodCutoff N s K γ ε X ≠ 0 → X ∈ goodEvent N s K γ ε) ∧
    (∀ ε : ℝ, 0 < ε → ∃ A C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (K : ℝ), 1 ≤ K →
      (∀ z : Fin (N : ℕ) → ℝ, gapCutoff N s K γ ε z = 1 →
        fderiv ℝ (gapCutoff N s K γ ε) z = 0) ∧
      (∀ z : Fin (N : ℕ) → ℝ, (∀ i : Fin (N : ℕ), 0 < z i) → z ∉ gapGoodEvent N s K γ ε →
        fderiv ℝ (gapCutoff N s K γ ε) z = 0) ∧
      (∀ᵐ z ∂(volume : Measure (Fin (N : ℕ) → ℝ)),
        Real.sqrt (∑ j : Fin (N : ℕ),
            (fderiv ℝ (gapCutoff N s K γ ε) z (Pi.single j (1 : ℝ))) ^ 2)
          ≤ C * K ^ A)) ∧
    (∀ (N : ℕ+) (ε K : ℝ) (X : Configuration N),
      goodCutoff N s K γ ε X =
        gapCutoff N s K γ ε (fun i : Fin (N : ℕ) => gap X ((i : ℕ) : ℤ))) := by
  obtain ⟨hprob, hcomp, hsupp, hgrad, hbridge⟩ :=
    Internal.aPrioriGood_complete_of_rigidity beta s hbeta hs hs1
      (Internal.rigidityConclusion_of_externals hBE hPL beta s hbeta hs hs1) γ hγ
  refine ⟨fun ε hε B hB => ?_, hcomp, hsupp, hgrad, hbridge⟩
  obtain ⟨C, hC, h⟩ := hprob ε hε B hB
  exact ⟨C, hC, h hPL⟩

end Riesz1

end
end
