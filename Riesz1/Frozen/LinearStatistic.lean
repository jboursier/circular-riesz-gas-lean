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
public import Riesz1.Frozen.Configuration

/-!
# Linear statistic: `Riesz1.linearStatistic`

Linear statistic of a real representative.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Linear statistic of a real representative. -/
def linearStatistic {N : ℕ+} (f : UnitAddCircle → ℝ) (X : Configuration N) : ℝ :=
  ∑ i : Fin (N : ℕ), f (X.val i : UnitAddCircle)


end Riesz1

end
end
