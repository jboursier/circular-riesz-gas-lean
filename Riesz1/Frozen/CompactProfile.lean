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
public import Riesz1.Frozen.Profile
public import Riesz1.Frozen.ZeroExtension

/-!
# Compact profile: `Riesz1.CompactProfile`

Compact essential support with a fixed margin. This is (A4) of Assumption 1.1.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Compact essential support with a fixed margin. This is (A4) of Assumption 1.1. -/
def CompactProfile (p : Profile) : Prop :=
  ∃ rho : ℝ, 0 < rho ∧ rho < 1 / 2 ∧
    ∀ᵐ x : ℝ, rho ≤ |x| → zeroExtension p x = 0


end Riesz1

end
end
