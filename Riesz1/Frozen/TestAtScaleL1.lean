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
public import Riesz1.Frozen.UnitLength
public import Riesz1.Frozen.Profile
public import Riesz1.Frozen.Scale
public import Riesz1.Frozen.TestAtScale
public import Riesz1.Frozen.RealL2Integrable
public import Riesz1.Frozen.TestAtScaleL2

/-!
# First-moment bound at a scale: `Riesz1.testAtScaleL1`

First-moment certificate derived from the fixed profile, at every scale.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- First-moment certificate derived from the fixed profile, at every scale. -/
theorem testAtScaleL1 (p : Profile) (ell : Scale) : Integrable (testAtScale p ell) volume :=
  realL2Integrable unitLength _ (testAtScaleL2 p ell)

end Riesz1

end
end
