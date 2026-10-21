/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopCutoffComplete
public import Riesz1.Auxiliary.LoopCutoffProbability
public import Riesz1.Rigidity.RigidityTheorem

/-!
# The loop cutoff, with the externals as hypotheses

Restatements of the conditional theorems
`Riesz1.Internal.auxiliary_Loop_cutoff_of_rigidity` and
`Riesz1.Internal.loopCutoff_probability_of_rigidity`. The rigidity hypothesis is replaced by the
externals `Riesz1.External.BakryEmery` and `Riesz1.External.PrekopaLeindler`.

The theorem `auxiliary_Loop_cutoff` states every claim of the cutoff part of Lemma 5.8.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction ContDiff

namespace Riesz1

/-- The cutoff part of Lemma 5.8, with the externals as hypotheses: the probability
bound, the gradient event, the bound on `F^*_γ`, and the envelopes of the transport. -/
theorem auxiliary_Loop_cutoff (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (β s α : ℝ) (hβ : 0 < β) (hs : 0 < s) (hs1 : s < 1)
    (hα : s - 1 ≤ α) (hα2 : α < s / 2)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4))
    (hχ1 : ∀ x : ℝ, |x| ≤ 1 / 8 → χ x = 1) (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    ∃ Cenv : ℝ, 0 ≤ Cenv ∧ ∀ γ ε B₀ : ℝ, 1 < γ → 0 < ε →
      ε < min (1 / 8) ((1 - s / 2) / 8) → 0 < B₀ →
      ∃ C B₁ : ℝ, B₁ = (1 - s + α) + 2 * γ + ε * (s + 1) ∧ 0 < C ∧ 0 < B₁ ∧
        ∀ (N : ℕ+) (ℓ : ℝ), 2 ≤ (N : ℕ) → 0 < ℓ → ℓ ≤ 1 → 1 ≤ (N : ℝ) * ℓ →
          gibbsMeasure ⟨(β, s), hβ, hs, hs1⟩ N
            {X | loopCutoff s γ ε N ℓ X.val ≠ 1} ≤
              ENNReal.ofReal (C * ((N : ℝ) * ℓ) ^ (-B₀)) ∧
          (∀ X : Configuration N, 0 < loopCutoff s γ ε N ℓ X.val →
            gradEvent s (2 * γ) ε N ℓ X.val) ∧
          ∀ (C0 : ℝ) (ψ : ℝ → ℝ), 0 ≤ C0 → ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
            (∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
            (∀ t, |deriv (deriv ψ) t| ≤ C0 * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
            (∀ y : Fin (N : ℕ) → ℝ, y ∈ orderedDomain N → y ⟨0, N.pos⟩ = 0 →
              |loopCutoffF χ s γ ε N ℓ ψ y| ≤ C * C0 * ((N : ℝ) * ℓ) ^ B₁) ∧
            (∀ t, |deriv (loopTransport χ N ℓ γ ψ) t| ≤
                Cenv * C0 * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t ∧
              |deriv (deriv (loopTransport χ N ℓ γ ψ)) t| ≤
                Cenv * C0 * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) := by
  obtain ⟨Cenv, hCenv, h⟩ := Internal.auxiliary_Loop_cutoff_of_rigidity β s α hβ hs hs1 hα hα2
    (Internal.rigidityConclusion_of_externals hBE hPL β s hβ hs hs1) hPL hχ hχc hχs hχ1 hχ01
  exact ⟨Cenv, hCenv, h⟩

/-- The probability bound `P(η ≠ 1) ≤ C K^{-B₀}` of the loop cutoff, with the externals as
hypotheses. -/
theorem loopCutoff_probability (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (β s : ℝ) (hβ : 0 < β) (hs : 0 < s) (hs1 : s < 1)
    (γ ε : ℝ) (hγ : 1 < γ) (hε : 0 < ε) (hε1 : ε < min (1 / 8) ((1 - s / 2) / 8))
    (B₀ : ℝ) (hB₀ : 0 < B₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+), 2 ≤ (N : ℕ) → ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ 1 → 1 ≤ (N : ℝ) * ℓ →
      gibbsMeasure ⟨(β, s), hβ, hs, hs1⟩ N {X : Configuration N | loopCutoff s γ ε N ℓ X.val ≠ 1} ≤
        ENNReal.ofReal (C * ((N : ℝ) * ℓ) ^ (-B₀)) :=
  Internal.loopCutoff_probability_of_rigidity β s hβ hs hs1 hPL
    (Internal.rigidityConclusion_of_externals hBE hPL β s hβ hs hs1) γ ε hγ hε hε1 B₀ hB₀

end Riesz1

end
end
