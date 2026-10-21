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
public import Riesz1.Frozen.RieszRepresentative

/-!
# Riesz kernel: `Riesz1.rieszKernel`

The pointwise kernel has no collision point.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- The pointwise kernel has no collision point. -/
def rieszKernel (s : RieszExponent) (x : {x : UnitAddCircle // x ≠ 0}) : ℝ :=
  rieszRepresentative s x.val


end Riesz1

end
end
