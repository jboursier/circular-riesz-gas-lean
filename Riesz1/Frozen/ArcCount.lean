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
# Arc count: `Riesz1.arcCount`

Open arc count.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Open arc count. -/
def arcCount {N : ℕ+} (center : UnitAddCircle) (a : ℝ) (X : Configuration N) : ℝ :=
  ∑ i : Fin (N : ℕ), if dist (X.val i : UnitAddCircle) center < a then 1 else 0


end Riesz1

end
end
