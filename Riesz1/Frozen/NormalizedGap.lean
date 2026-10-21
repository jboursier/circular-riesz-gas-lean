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
public import Riesz1.Frozen.Configuration
public import Riesz1.Frozen.CyclicLift
public import Riesz1.Frozen.PeriodicZeta

/-!
# Normalized gap: `Riesz1.normalizedGap`

Normalized gap based at paper label 1. This is the gap in Corollary 1 of the paper.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Normalized gap based at paper label 1. This is the gap in Corollary 1 of the paper. -/
def normalizedGap (P : Parameters) (N : ℕ+) (k : ℕ) (_hk : 1 ≤ k ∧ k ≤ (N : ℕ) / 2) (X : Configuration N) : ℝ :=
  ((N : ℝ) * (cyclicLift X k - cyclicLift X 0) - k) /
    Real.sqrt ((N : ℝ) ^ P.val.2 * periodicZeta (parametersExponent P) (((k : ℝ) / (N : ℝ) : ℝ) : UnitAddCircle))


end Riesz1

end
end
