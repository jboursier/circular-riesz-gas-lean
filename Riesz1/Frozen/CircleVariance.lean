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
public import Riesz1.Frozen.ParametersExponent
public import Riesz1.Frozen.RieszConstant
public import Riesz1.Frozen.Profile
public import Riesz1.Frozen.Scale
public import Riesz1.Frozen.CircleSobolevSq
public import Riesz1.Frozen.TestAtScale
public import Riesz1.Frozen.TestAtScaleL2

/-!
# Circle variance: `Riesz1.circleVariance`

Circle variance parameter as an extended nonnegative real.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Circle variance parameter as an extended nonnegative real. -/
def circleVariance (P : Parameters) (p : Profile) (ell : Scale) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 * Real.pi) ^ (1 - P.val.2) / (2 * P.val.1 * rieszConstant (parametersExponent P)) * ell.val ^ (-P.val.2)) *
    circleSobolevSq ((1 - P.val.2) / 2) ⟨(fun x => (testAtScale p ell x : ℂ)), testAtScaleL2 p ell⟩


end Riesz1

end
end
