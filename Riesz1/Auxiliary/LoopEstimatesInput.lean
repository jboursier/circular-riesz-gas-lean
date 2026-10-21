/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopLocalMomentsDefs
public import Riesz1.Auxiliary.LoopCutoffDefs
public import Riesz1.Auxiliary.LoopLocalizationExponent

/-!
# The anchoring input

The first assertion of the anchoring part of Lemma 5.8, on the
preceding-particle carrier. The two small-parameter constants precede
the inverse temperature and the spatial cutoff, expressing their dependence
only on `s, α, γ`. The norm is extended valued, so its bound also certifies
the finite second moment of the error.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff ENNReal

namespace Riesz1.Internal

/-- Precisely the `L²` assertion of
the anchoring part of Lemma 5.8. Here `N = n + 2`. Every `N ≥ 2` occurs.
No assertion about localization or about variance is included in this input. -/
def LoopAnchoringL2Input : Prop :=
  ∀ (s α γ : ℝ), 0 < s → s < 1 → s - 1 ≤ α → α < s / 2 →
    loopLocalizationExponent s ≤ γ →
    ∃ ε₀ κ : ℝ, 0 < ε₀ ∧ 0 < κ ∧
      ∀ (β : ℝ) (hβ : 0 < β) (hs : 0 < s) (hs1 : s < 1)
        (χ : ℝ → ℝ), ContDiff ℝ ∞ χ → HasCompactSupport χ →
        tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4) →
        (∀ x : ℝ, |x| ≤ 1 / 8 → χ x = 1) →
        (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
        ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ∃ C : ℝ, 0 < C ∧ ∀ (C₀ : ℝ), 0 ≤ C₀ →
          ∀ (n : ℕ) (ℓ : ℝ) (ψ : ℝ → ℝ),
            0 < ℓ → ℓ ≤ 1 → 1 ≤ ((n + 1).succPNat : ℝ) * ℓ →
            ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
            (∀ t, |deriv ψ t| ≤ C₀ * gradWeightOne s (1 - s + α)
              (((n + 1).succPNat : ℝ) * ℓ) ℓ⁻¹ t) →
            (∀ t, |deriv (deriv ψ) t| ≤ C₀ * gradWeightTwo s (1 - s + α)
              (((n + 1).succPNat : ℝ) * ℓ) ℓ⁻¹ t) →
            let N := (n + 1).succPNat
            let P : Parameters := ⟨(β, s), hβ, hs, hs1⟩
            eLpNorm (fun X : LoopPrecedingConfiguration N =>
              loopLocalLoop s N ℓ γ (loopLocalTransport χ N ℓ γ ψ) X -
                loopCutoffF χ s γ ε N ℓ ψ (anchorVector (loopPrecedingOffsets X)))
              2 (loopPrecedingMeasure P N) ≤
                ENNReal.ofReal (C * C₀ * ((N : ℝ) * ℓ) ^ ((1 - s + α) + κ * ε))

end Riesz1.Internal

end
