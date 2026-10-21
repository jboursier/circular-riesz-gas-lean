/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1Audit.AlmostOptimalRigidity.SolutionBasic
public import Riesz1.Frozen.AlmostOptimalRigidity

/-!
# Theorem 1 (near-optimal rigidity): the proof

The statement of the challenge, on the definitions of `SolutionBasic.lean`, proved from
`Riesz1.almost_optimal_rigidity` of the library. The definitions of the challenge are copies of
those of the library, so the two statements agree after unfolding the definitions.
-/

@[expose] public section

namespace Riesz1Audit.AlmostOptimalRigidity

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Near-optimal rigidity: both gaps and arbitrary-center interval discrepancy,
with the same c,C chosen before N. This is Theorem 1 of the paper. -/
theorem almost_optimal_rigidity :
  ∀ (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1),
    let P : Parameters := ⟨(beta, s), hbeta, hs, hs1⟩
    ModelWellDefined P ∧
    ∃ eps0 : ℝ, 0 < eps0 ∧ ∀ eps : ℝ, 0 < eps → eps < eps0 →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
        ∀ N : ℕ+,
          (∀ (i : Fin (N : ℕ)) (k : ℕ), 1 ≤ k → k ≤ (N : ℕ) / 2 →
            gibbsMeasure P N {X |
              |(N : ℝ) * (cyclicLift X ((i.val : ℤ) + k) - cyclicLift X i.val) - k| ≥
                (k : ℝ) ^ (s / 2 + eps)} ≤
              ENNReal.ofReal (C * Real.exp (-c * (k : ℝ) ^ (eps / (4 * (s + 2)))))) ∧
          (∀ (x : UnitAddCircle) (ell : ℝ), 0 < ell → ell ≤ 1 / 4 →
            gibbsMeasure P N {X |
              |arcCount x ell X - 2 * (N : ℝ) * ell| ≥
                ((N : ℝ) * ell) ^ (s / 2 + eps)} ≤
              ENNReal.ofReal (C * Real.exp (-c * ((N : ℝ) * ell) ^ (eps / (4 * (s + 2)))))) :=
  by exact _root_.Riesz1.almost_optimal_rigidity

end Riesz1

end

end Riesz1Audit.AlmostOptimalRigidity

end
