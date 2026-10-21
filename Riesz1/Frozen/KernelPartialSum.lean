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
# Kernel partial sums: `Riesz1.kernelPartialSum`

Symmetric renormalized partial sums.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Symmetric renormalized partial sums. -/
def kernelPartialSum (s : RieszExponent) (x : {x : ℝ // (x : UnitAddCircle) ≠ 0}) (M : ℕ) : ℝ :=
  (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), |(k : ℝ) + x.val| ^ (-s.val)) -
    2 * (M : ℝ) ^ (1 - s.val) / (1 - s.val)


end Riesz1

end
end
