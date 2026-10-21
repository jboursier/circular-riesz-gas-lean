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
public import Riesz1.Frozen.Length
public import Riesz1.Frozen.Circle
public import Riesz1.Frozen.Arclength

/-!
# Convolution: `Riesz1.convolution`

Arclength convolution.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Arclength convolution. -/
def convolution (L : Length) (f g : Circle L → ℂ)
    (x : {x : Circle L // Integrable (fun y => f (x - y) * g y) (arclength L)}) : ℂ :=
  ∫ y, f (x.val - y) * g y ∂arclength L


end Riesz1

end
end
