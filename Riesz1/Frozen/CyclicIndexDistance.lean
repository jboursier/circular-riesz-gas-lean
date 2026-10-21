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
public import Mathlib.Data.Nat.Dist

/-!
# Cyclic index distance: `Riesz1.cyclicIndexDistance`

Cyclic distance between labels.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Cyclic distance between labels. -/
def cyclicIndexDistance (N : ℕ+) (i j : Fin (N : ℕ)) : ℕ :=
  min (Nat.dist i.val j.val) ((N : ℕ) - Nat.dist i.val j.val)


end Riesz1

end
end
