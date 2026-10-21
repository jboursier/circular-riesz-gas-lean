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
public import Riesz1.Frozen.Profile
public import Riesz1.Frozen.Scale
public import Riesz1.Frozen.RescaledProfile

/-!
# Test function at a scale: `Riesz1.testAtScale`

Actual unit-circle test at a given scale.
The branch at scale one uses the general macroscopic profile.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Actual unit-circle test at a given scale.
The branch at scale one uses the general macroscopic profile. -/
def testAtScale (p : Profile) (ell : Scale) : UnitAddCircle → ℝ :=
  if ell.val = 1 then p.val else rescaledProfile p ell


end Riesz1

end
end
