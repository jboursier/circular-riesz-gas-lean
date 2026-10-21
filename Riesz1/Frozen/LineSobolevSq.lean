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
# Sobolev seminorm on the line: `Riesz1.lineSobolevSq`

Line homogeneous Sobolev seminorm using the L² Fourier isometry.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Line homogeneous Sobolev seminorm using the L² Fourier isometry. -/
def lineSobolevSq (r : ℝ) (f : Lp ℂ 2 (volume : Measure ℝ)) : ℝ≥0∞ :=
  ∫⁻ eta : ℝ, ENNReal.ofReal (|eta| ^ (2 * r) * ‖Lp.fourierTransformₗᵢ ℝ ℂ f eta‖ ^ 2)


end Riesz1

end
end
