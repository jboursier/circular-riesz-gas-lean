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
public import Riesz1.Frozen.LineSobolevSq

/-!
# Line variance: `Riesz1.lineVariance`

Line variance parameter.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Line variance parameter. -/
def lineVariance (P : Parameters) (f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 * Real.pi) ^ (1 - P.val.2) / (2 * P.val.1 * rieszConstant (parametersExponent P))) *
    lineSobolevSq ((1 - P.val.2) / 2) f


end Riesz1

end
end
