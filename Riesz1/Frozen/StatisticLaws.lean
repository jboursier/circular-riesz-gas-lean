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
public import Riesz1.Frozen.GibbsMeasure
public import Riesz1.Frozen.Profile
public import Riesz1.Frozen.Scales
public import Riesz1.Frozen.ParticleNumber
public import Riesz1.Frozen.NormalizedStatistic

/-!
# Laws of the statistics: `Riesz1.statisticLaws`

Laws of the CLT variables (see Theorem 3).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Laws of the CLT variables (see Theorem 3). -/
def statisticLaws (P : Parameters) (p : Profile) (ell : Scales) (n : ℕ) : Measure ℝ :=
  (gibbsMeasure P (particleNumber n)).map (normalizedStatistic P p ell (particleNumber n))


end Riesz1

end
end
