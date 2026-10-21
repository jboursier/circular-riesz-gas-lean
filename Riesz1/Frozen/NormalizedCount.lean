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
public import Riesz1.Frozen.ArcCount
public import Riesz1.Frozen.Scales
public import Riesz1.Frozen.PeriodicZeta

/-!
# Normalized count: `Riesz1.normalizedCount`

Normalized interval discrepancy, as in Corollary 1.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Normalized interval discrepancy, as in Corollary 1. -/
def normalizedCount (P : Parameters) (a : ℝ) (_ha : 0 < a) (_ha1 : a < 1 / 2) (ell : Scales) (N : ℕ+)
    (X : Configuration N) : ℝ :=
  (arcCount 0 (a * (ell N).val) X - 2 * a * (N : ℝ) * (ell N).val) /
    Real.sqrt ((N : ℝ) ^ P.val.2 * periodicZeta (parametersExponent P) ((2 * a * (ell N).val : ℝ) : UnitAddCircle))


end Riesz1

end
end
