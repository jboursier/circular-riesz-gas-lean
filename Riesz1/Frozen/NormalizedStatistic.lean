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
public import Riesz1.Frozen.Configuration
public import Riesz1.Frozen.Fluctuation
public import Riesz1.Frozen.Profile
public import Riesz1.Frozen.Scales
public import Riesz1.Frozen.TestAtScale
public import Riesz1.Frozen.TestAtScaleL1

/-!
# Normalized statistic: `Riesz1.normalizedStatistic`

Normalized centered statistic. This is the statistic in Theorem 3 of the paper.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Normalized centered statistic. This is the statistic in Theorem 3 of the paper. -/
def normalizedStatistic (P : Parameters) (p : Profile) (ell : Scales)
    (N : ℕ+) (X : Configuration N) : ℝ :=
  ((N : ℝ) * (ell N).val) ^ (-P.val.2 / 2) * fluctuation ⟨testAtScale p (ell N), testAtScaleL1 p (ell N)⟩ X


end Riesz1

end
end
