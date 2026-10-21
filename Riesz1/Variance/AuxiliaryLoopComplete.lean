/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.AuxiliaryLoop
public import Riesz1.Auxiliary.LoopEstimatesAnchoring

/-!
# Loop localization estimates, unconditional form

Lemma 5.8 and its estimates. The anchoring input of
`Internal.auxiliary_Loop_estimates_of_anchoring` is discharged by
`Internal.loopAnchoringL2Input_of_externals`.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace Riesz1

open Internal

/-- The estimates part of Lemma 5.8. -/
theorem auxiliary_Loop_estimates
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (s α γ : ℝ) (hs : 0 < s) (hs1 : s < 1)
    (hα : s - 1 ≤ α) (hα2 : α < s / 2)
    (hγ : loopLocalizationExponent s ≤ γ) :
    ∃ ε₀ κ : ℝ, 0 < ε₀ ∧ 0 < κ ∧
      ∀ (β : ℝ) (hβ : 0 < β) (χ : ℝ → ℝ),
        ContDiff ℝ ∞ χ → HasCompactSupport χ →
        tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4) →
        (∀ x : ℝ, |x| ≤ 1 / 8 → χ x = 1) → (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
        ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (ℓ C₀ : ℝ) (ψ : ℝ → ℝ),
          0 < ℓ → ℓ ≤ 1 → 1 ≤ ((n + 1).succPNat : ℝ) * ℓ → 0 ≤ C₀ →
          ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
          (∀ t, |deriv ψ t| ≤ C₀ * gradWeightOne s (1 - s + α)
            (((n + 1).succPNat : ℝ) * ℓ) ℓ⁻¹ t) →
          (∀ t, |deriv (deriv ψ) t| ≤ C₀ * gradWeightTwo s (1 - s + α)
            (((n + 1).succPNat : ℝ) * ℓ) ℓ⁻¹ t) →
          let N := (n + 1).succPNat
          let K := (N : ℝ) * ℓ
          let P : Parameters := ⟨(β, s), hβ, hs, hs1⟩
          letI := (modelWellDefined P N).2.2
          letI := isProbabilityMeasure_anchoredLaw P (n + 1)
          let F := fun X : Configuration N => loopFunctional s (N : ℕ) (loopScaleField ℓ ψ) X.val
          let H := fun y => loopCutoffF χ s γ ε N ℓ ψ (anchorVector y)
          ∃ hF : MemLp F 2 (gibbsMeasure P N),
          ∃ hH : MemLp H 2 (anchoredLaw P (n + 1)),
            variance (gibbsMeasure P N) F (hF.integrable one_le_two) ≤
              ENNReal.ofReal (C * K ^ (κ * ε)) *
                variance (anchoredLaw P (n + 1)) H (hH.integrable one_le_two) +
              ENNReal.ofReal (C * C₀ ^ 2 * K ^ (κ * ε) * (K + K ^ (2 * (1 - s + α)))) :=
  auxiliary_Loop_estimates_of_anchoring (loopAnchoringL2Input_of_externals hBE hPL) hBE hPL
    s α γ hs hs1 hα hα2 hγ

/-- Lemma 5.8. -/
theorem auxiliary_Loop
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (s α γ : ℝ) (hs : 0 < s) (hs1 : s < 1)
    (hα : s - 1 ≤ α) (hα2 : α < s / 2)
    (hγ : loopLocalizationExponent s ≤ γ) :
    ∃ ε₀ κ : ℝ, 0 < ε₀ ∧ 0 < κ ∧
      ∀ (β : ℝ) (hβ : 0 < β) (χ : ℝ → ℝ),
        ContDiff ℝ ∞ χ → HasCompactSupport χ →
        tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4) →
        (∀ x : ℝ, |x| ≤ 1 / 8 → χ x = 1) → (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
        ∀ C₀ : ℝ, 0 ≤ C₀ → ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (ℓ : ℝ) (ψ : ℝ → ℝ),
          0 < ℓ → ℓ ≤ 1 → 1 ≤ ((n + 1).succPNat : ℝ) * ℓ →
          ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
          (∀ t, |deriv ψ t| ≤ C₀ * gradWeightOne s (1 - s + α)
            (((n + 1).succPNat : ℝ) * ℓ) ℓ⁻¹ t) →
          (∀ t, |deriv (deriv ψ) t| ≤ C₀ * gradWeightTwo s (1 - s + α)
            (((n + 1).succPNat : ℝ) * ℓ) ℓ⁻¹ t) →
          let N := (n + 1).succPNat
          let K := (N : ℝ) * ℓ
          let P : Parameters := ⟨(β, s), hβ, hs, hs1⟩
          letI := (modelWellDefined P N).2.2
          letI := isProbabilityMeasure_anchoredLaw P (n + 1)
          let F := fun X : Configuration N => loopFunctional s (N : ℕ) (loopScaleField ℓ ψ) X.val
          let H := fun y => loopCutoffF χ s γ ε N ℓ ψ (anchorVector y)
          ∃ hF : MemLp F 2 (gibbsMeasure P N),
          ∃ hH : MemLp H 2 (anchoredLaw P (n + 1)),
            variance (gibbsMeasure P N) F (hF.integrable one_le_two) ≤
              ENNReal.ofReal (C * K ^ (κ * ε)) *
                variance (anchoredLaw P (n + 1)) H (hH.integrable one_le_two) +
              ENNReal.ofReal (C * K ^ (κ * ε) * (K + K ^ (2 * (1 - s + α)))) :=
  auxiliary_Loop_of_anchoring (loopAnchoringL2Input_of_externals hBE hPL) hBE hPL
    s α γ hs hs1 hα hα2 hγ

end Riesz1

end
