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
# Periodic zeta function: `Riesz1.periodicZeta`

Periodic zeta combination.
At zero the subtraction is identically zero without assigning a collision value.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Periodic zeta combination.
At zero the subtraction is identically zero without assigning a collision value. -/
def periodicZeta (s : RieszExponent) (t : UnitAddCircle) : ℝ :=
  2 * ((HurwitzZeta.hurwitzZetaEven t (-s.val : ℂ)).re -
    (HurwitzZeta.hurwitzZetaEven 0 (-s.val : ℂ)).re)


end Riesz1

end
end
