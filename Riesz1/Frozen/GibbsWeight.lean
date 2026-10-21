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
public import Riesz1.Frozen.ParametersExponent
public import Riesz1.Frozen.Configuration
public import Riesz1.Frozen.Energy
public import Riesz1.Frozen.ConfigurationVolume

/-!
# Gibbs weight: `Riesz1.gibbsWeight`

Unnormalized Gibbs measure.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Unnormalized Gibbs measure. -/
def gibbsWeight (P : Parameters) (N : ℕ+) : Measure (Configuration N) :=
  (configurationVolume N).withDensity (fun X => ENNReal.ofReal (Real.exp (-P.val.1 * energy (parametersExponent P) X)))


end Riesz1

end
end
