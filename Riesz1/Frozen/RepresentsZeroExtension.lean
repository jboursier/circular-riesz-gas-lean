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
# Zero extension in L²: `Riesz1.RepresentsZeroExtension`

Representation of a compact profile's zero extension in L².
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Representation of a compact profile's zero extension in L². -/
def RepresentsZeroExtension (p : Profile) (f : Lp ℂ 2 (volume : Measure ℝ)) : Prop :=
  (fun x => f x) =ᵐ[volume] (fun x => (zeroExtension p x : ℂ))


end Riesz1

end
end
