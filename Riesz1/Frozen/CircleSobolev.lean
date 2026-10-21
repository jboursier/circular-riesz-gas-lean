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
public import Riesz1.Frozen.CircleSobolevSq

/-!
# Sobolev membership on the circle: `Riesz1.CircleSobolev`

H^r membership requires L² and finite seminorm.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- H^r membership requires L² and finite seminorm. -/
def CircleSobolev (r : ℝ) (f : UnitAddCircle → ℂ) : Prop :=
  ∃ hf : MemLp f 2 volume, circleSobolevSq r ⟨f, hf⟩ < ⊤


end Riesz1

end
end
