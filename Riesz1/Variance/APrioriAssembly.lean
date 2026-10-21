/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriAssemblyScaling
public import Riesz1.Variance.APrioriAssemblyMembership

/-!
# The anchored a priori variance bound

The first assertion of Lemma 5.2, at the original center
and radius, for every particle number and with the factor `M²`.
Completion membership is proved in `APrioriAssemblyMembership`.
The Bakry–Émery criterion `External.BakryEmery` and the Prékopa–Leindler inequality
`External.PrekopaLeindler` are the only hypotheses beyond the
parameters and assumptions on the test function.

This file does not assert the combined lemma: the spatial-origin bound
and the translated and changed-radius clauses are separate steps.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1.Internal

/-- The anchored bound of Lemma 5.2, with the actual completion
membership discharged and the order of quantifiers of the paper. -/
theorem a_priori_anchored
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) (lam ε : ℝ) (hlam : 0 ≤ lam) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ : ℝ), 0 < ℓ → ℓ ≤ 1 → 1 ≤ (N : ℝ) * ℓ →
      ∀ M : ℝ, 0 ≤ M → ∀ f : ℝ → ℝ,
      ContDiff ℝ 1 f → Function.Periodic f (1 / ℓ) →
      (∀ u ∈ Icc (-(1 / ℓ / 2)) (1 / ℓ / 2),
        |deriv f u| ≤ M * cutoffMajorant P.val.2 lam ((N : ℝ) * ℓ) |u|) →
      ∃ hF : Integrable (fun X : Configuration N =>
          ∑ i, f ((X.val i - X.val ⟨0, N.pos⟩) / ℓ)) (gibbsMeasure P N),
        Riesz1.variance (gibbsMeasure P N) (fun X =>
          ∑ i, f ((X.val i - X.val ⟨0, N.pos⟩) / ℓ)) hF ≤
          ENNReal.ofReal (C * M ^ 2 * ((N : ℝ) * ℓ) ^ (ε + max (2 * lam) P.val.2)) :=
  a_priori_anchored_of_membership hBE hPL a_priori_membership_input P lam ε hlam hε

end Riesz1.Internal

end
