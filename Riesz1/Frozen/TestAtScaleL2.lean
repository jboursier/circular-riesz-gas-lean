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
public import Riesz1.Frozen.TestAtScale
public import Riesz1.Frozen.RescaledProfileL2

/-!
# Tests at a scale lie in L²: `Riesz1.testAtScaleL2`

Every actual test is L², with the certificate derived from Profile.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Every actual test is L², with the certificate derived from Profile. -/
theorem testAtScaleL2 (p : Profile) (ell : Scale) :
    MemLp (fun x => (testAtScale p ell x : ℂ)) 2 volume := by
  unfold testAtScale
  split_ifs
  · exact p.property
  · exact rescaledProfileL2 p ell

end Riesz1

end
end
