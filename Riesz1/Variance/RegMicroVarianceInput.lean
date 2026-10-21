/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Frozen.Scale
public import Riesz1.Frozen.ObservationLength
public import Riesz1.Frozen.CentralRep
public import Riesz1.Frozen.GibbsMeasure
public import Riesz1.Frozen.Variance
public import Riesz1.ToMathlib.Calculus.CutoffMajorant

/-!
# The spatial clause of the a priori lemma used by microscopic variance

This proposition states the spatial-origin clause of the a priori lemma
(Lemma 5.2). Results that need it take it as an explicit hypothesis.
It includes the factor `M²`, translation, and constants chosen before the
test, particle number and observation scale. No proof of the a priori
lemma is asserted here.

Only the radius-two version is needed here: the fixed cutoff supports
in the microscopic proof lie within this radius. `cutoffMajorant` and
the central circular representative are the existing objects.
-/

@[expose] public section

open MeasureTheory

namespace Riesz1.Internal

/-- The needed assertion of Lemma 5.2, on the circle,
Gibbs law and extended variance. The smooth test is evaluated directly
on the circle. Its singular envelope may have any center. -/
def RegMicroAPrioriInput : Prop :=
  ∀ (P : Parameters) (lam : ℝ), 0 ≤ lam → ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ : Scale), 1 ≤ (N : ℝ) * ℓ.val →
      ∀ (M : ℝ), 0 ≤ M → ∀ (c : ℝ) (f : Circle (observationLength ℓ) → ℝ),
        ContDiff ℝ 1 (fun u : ℝ => f (u : Circle (observationLength ℓ))) →
        (∀ u : ℝ, |deriv (fun t : ℝ => f (t : Circle (observationLength ℓ))) u| ≤
          M * cutoffMajorant P.val.2 lam ((N : ℝ) * ℓ.val)
            |centralRep (observationLength ℓ) ((u - c : ℝ) : Circle (observationLength ℓ))|) →
        ∃ hF : Integrable (fun X : Configuration N =>
            ∑ i : Fin (N : ℕ), f ((X.val i / ℓ.val : ℝ) : Circle (observationLength ℓ)))
              (gibbsMeasure P N),
          variance (gibbsMeasure P N)
            (fun X => ∑ i : Fin (N : ℕ), f ((X.val i / ℓ.val : ℝ) : Circle (observationLength ℓ))) hF ≤
              ENNReal.ofReal (C * M ^ 2 * ((N : ℝ) * ℓ.val) ^ (ε + max (2 * lam) P.val.2))

end Riesz1.Internal
