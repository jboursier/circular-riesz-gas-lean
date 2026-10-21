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
public import Riesz1.Frozen.UnitLength
public import Riesz1.Frozen.CentralRep
public import Riesz1.Frozen.Profile
public import Riesz1.Frozen.ZeroExtension
public import Riesz1.Frozen.Scale

/-!
# Rescaled profile: `Riesz1.rescaledProfile`

Pullback of the periodized compact profile to the unit circle.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Pullback of the periodized compact profile to the unit circle. -/
def rescaledProfile (p : Profile) (ell : Scale) (x : UnitAddCircle) : ℝ :=
  zeroExtension p (centralRep unitLength x / ell.val)


end Riesz1

end
end
