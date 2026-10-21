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
public import Riesz1.Frozen.Scales

/-!
# Mesoscopic scales: `Riesz1.Mesoscopic`

Nℓ_N tends to infinity.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Nℓ_N tends to infinity. -/
def Mesoscopic (ell : Scales) : Prop :=
  Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * (ell ⟨n + 1, Nat.succ_pos n⟩).val) atTop atTop


end Riesz1

end
end
