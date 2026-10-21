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
public import Riesz1.Frozen.PowerExponent
public import Riesz1.Frozen.PowerRieszExponent

/-!
# Power-law variance: `Riesz1.powerVariance`

Power-law limiting variance. This is the variance in Corollary 2 of the paper.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Power-law limiting variance. This is the variance in Corollary 2 of the paper. -/
def powerVariance (P : Parameters) (alpha : PowerExponent P) : ℝ :=
  (2 * Real.pi) ^ (-1 + 2 * alpha.val - P.val.2) *
    rieszConstant (powerRieszExponent P alpha) ^ 2 / (P.val.1 * rieszConstant (parametersExponent P)) *
      (HurwitzZeta.hurwitzZeta 0 ((1 + P.val.2 - 2 * alpha.val : ℝ) : ℂ)).re


end Riesz1

end
end
