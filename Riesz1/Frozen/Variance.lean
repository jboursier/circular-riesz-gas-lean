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
# Variance: `Riesz1.variance`

The squared centered integral, possibly infinite, with first-moment validity
asserted separately.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- The squared centered integral, possibly infinite, with first-moment validity
asserted separately. -/
def variance {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω) (F : Ω → ℝ) (_hF : Integrable F mu) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal ((F x - ∫ y, F y ∂mu) ^ 2) ∂mu


end Riesz1

end
end
