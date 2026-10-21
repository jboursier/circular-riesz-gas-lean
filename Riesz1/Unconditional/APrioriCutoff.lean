/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriCutoffL2
public import Riesz1.Rigidity.RigidityTheorem

/-!
# The anchored cutoff in `L²`, with the externals as hypotheses

Restatement of the conditional theorem
`Riesz1.Internal.anchoredCutoff_L2_of_rigidity`. The rigidity hypothesis is replaced by the
externals `Riesz1.External.BakryEmery` and `Riesz1.External.PrekopaLeindler`, and the
inner `∀ (_hPL : External.PrekopaLeindler)` binder is removed.

This is the second conclusion of Lemma 5.2. The first conclusion, the inverse-energy bound,
is not formalized, so Lemma 5.2 is not covered as a whole.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Riesz1

/-- The `L²` norm of `(1 - η*) T` under the anchored law is at most `C K^{-b}`, with the
externals as hypotheses. -/
theorem anchoredCutoff_L2 (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1) (γ ε : ℝ) (hγ : 1 < γ)
    (hε : 0 < ε) (D M b : ℝ) (hD : 0 < D) (hM : 0 < M) (hb : 0 < b) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ : ℝ), 2 ≤ (N : ℕ) → 0 < ℓ → ℓ ≤ 1 →
      1 ≤ ((N : ℕ) : ℝ) * ℓ →
      ∀ T : (Fin ((N : ℕ) - 1) → ℝ) → ℝ, Measurable T →
        (∀ y, |T y| ≤ M * (((N : ℕ) : ℝ) * ℓ) ^ D) →
        eLpNorm (fun y => (1 - anchoredCutoff N s (((N : ℕ) : ℝ) * ℓ) γ ε y) * T y) 2
            ((gibbsMeasure ⟨(beta, s), hbeta, hs, hs1⟩ N).map (anchorMap N))
          ≤ ENNReal.ofReal (C * (((N : ℕ) : ℝ) * ℓ) ^ (-b)) := by
  obtain ⟨C, hC, h⟩ := Internal.anchoredCutoff_L2_of_rigidity beta s hbeta hs hs1
    (Internal.rigidityConclusion_of_externals hBE hPL beta s hbeta hs hs1) γ ε hγ hε D M b hD hM hb
  exact ⟨C, hC, h hPL⟩

end Riesz1

end
end
