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
public import Riesz1.Frozen.Parameters

/-!
# Count variance: `Riesz1.countVariance`

Count and gap limiting variance. This is the variance in Corollary 1 of the paper.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Count and gap limiting variance. This is the variance in Corollary 1 of the paper. -/
def countVariance (P : Parameters) : ℝ :=
  Real.cos (Real.pi * P.val.2 / 2) / Real.sin (Real.pi * P.val.2 / 2) /
    (2 * P.val.1 * Real.pi * P.val.2)


end Riesz1

end
end
