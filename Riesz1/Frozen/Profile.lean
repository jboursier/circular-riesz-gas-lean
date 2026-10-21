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

/-!
# Profile: `Riesz1.Profile`

Fixed real L² profile with an explicit representative, as in Assumption 1.1.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Fixed real L² profile with an explicit representative, as in Assumption 1.1. -/
@[reducible] def Profile : Type :=
  {f : UnitAddCircle → ℝ // MemLp (fun x => (f x : ℂ)) 2 volume}

end Riesz1

end
end
