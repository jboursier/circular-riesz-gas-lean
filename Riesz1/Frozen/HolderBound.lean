/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
public import Mathlib.Tactic
public import Riesz1.Frozen.Length
public import Riesz1.Frozen.Circle

/-!
# Hölder bound: `Riesz1.HolderBound`

Global Hölder regularity with a quantitative bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Global Hölder regularity with a quantitative bound. -/
def HolderBound (L : Length) (r B : ℝ) (f : Circle L → ℝ) : Prop := by
  haveI : Fact (0 < L.val) := ⟨L.property⟩
  exact
  Continuous f ∧ (∀ x, |f x| ≤ B) ∧
    ∀ x y, |f x - f y| ≤ B * dist x y ^ r


end Riesz1

end
end
