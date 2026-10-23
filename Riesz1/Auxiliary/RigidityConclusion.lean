/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Frozen.GibbsMeasure
public import Riesz1.Frozen.CyclicLift
public import Riesz1.Frozen.ArcCount

/-!
# The rigidity conclusion as a hypothesis

The rigidity conclusion of Theorem 1, used conditionally by the loop moment
estimates of the moments and arcs parts of Lemma B.2.

The statement `Riesz1.almost_optimal_rigidity` gives this conclusion. Results that use it take
it as an explicit hypothesis `Riesz1.Internal.RigidityConclusion`, whose body is the second
conjunct of that statement, with the same parameter value.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

namespace Internal

/-- The near-optimal rigidity conclusion for the parameters `(beta, s)`: the gap bounds
and the arc-count bounds, with one threshold `eps0` and one pair of constants `c, C`
for each `eps`, chosen before `N`.

The proof of this conjunct is
`(almost_optimal_rigidity beta s hbeta hs hs1).2`, and it closes this statement by `exact`.
The body repeats the second conjunct of `Riesz1.almost_optimal_rigidity` symbol for symbol. -/
def RigidityConclusion (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1) : Prop :=
  let P : Parameters := ⟨(beta, s), hbeta, hs, hs1⟩
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
            ENNReal.ofReal (C * Real.exp (-c * ((N : ℝ) * ell) ^ (eps / (4 * (s + 2))))))

end Internal

end Riesz1

end
end
