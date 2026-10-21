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
public import Riesz1.Frozen.LinearStatistic

/-!
# Fluctuation: `Riesz1.fluctuation`

Lebesgue-centered statistic.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Lebesgue-centered statistic. -/
def fluctuation {N : ℕ+} (f : {f : UnitAddCircle → ℝ // Integrable f volume}) (X : Configuration N) : ℝ :=
  linearStatistic f.val X - (N : ℝ) * ∫ x, f.val x


end Riesz1

end
end
