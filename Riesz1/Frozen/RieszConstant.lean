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
public import Riesz1.Frozen.RieszExponent

/-!
# Riesz constant: `Riesz1.rieszConstant`

Riesz normalization.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Riesz normalization. -/
def rieszConstant (s : RieszExponent) : ℝ :=
  2 ^ (1 - s.val) * Real.sqrt Real.pi * Real.Gamma ((1 - s.val) / 2) / Real.Gamma (s.val / 2)


end Riesz1

end
end
