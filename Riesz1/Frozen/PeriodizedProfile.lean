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
public import Riesz1.Frozen.Length
public import Riesz1.Frozen.Circle
public import Riesz1.Frozen.CentralRep
public import Riesz1.Frozen.Profile
public import Riesz1.Frozen.ZeroExtension

/-!
# Periodized profile: `Riesz1.periodizedProfile`

Periodization of a supported profile on a positive-length circle,
using the central fundamental interval.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Periodization of a supported profile on a positive-length circle,
using the central fundamental interval. -/
def periodizedProfile (p : Profile) (L : Length) (x : Circle L) : ℝ :=
  ∑' n : ℤ, zeroExtension p (centralRep L x + (n : ℝ) * L.val)


end Riesz1

end
end
