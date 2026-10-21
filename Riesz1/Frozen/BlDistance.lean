/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
public import Mathlib.Tactic
public import Riesz1.Frozen.BLTest

/-!
# Bounded-Lipschitz distance: `Riesz1.blDistance`

Extended nonnegative bounded-Lipschitz distance.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Extended nonnegative bounded-Lipschitz distance. -/
def blDistance (mu nu : ProbabilityMeasure ℝ) : ℝ≥0∞ :=
  ⨆ f : {f : ℝ → ℝ // BLTest f},
    ENNReal.ofReal |(∫ x, f.val x ∂mu) - ∫ x, f.val x ∂nu|


end Riesz1

end
end
