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
# Circle Sobolev seminorm: `Riesz1.circleSobolevSq`

Circle homogeneous Sobolev seminorm squared, permitting infinity.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Circle homogeneous Sobolev seminorm squared, permitting infinity. -/
def circleSobolevSq (r : ℝ) (f : {f : UnitAddCircle → ℂ // MemLp f 2 volume}) : ℝ≥0∞ :=
  ∑' k : ℤ, if k = 0 then 0 else ENNReal.ofReal (|(k : ℝ)| ^ (2 * r) * ‖fourierCoeff f.val k‖ ^ 2)


end Riesz1

end
end
