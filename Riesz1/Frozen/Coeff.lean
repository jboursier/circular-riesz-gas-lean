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
public import Riesz1.Frozen.Arclength

/-!
# Fourier coefficients: `Riesz1.coeff`

Normalized Fourier coefficients on integrable functions.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Normalized Fourier coefficients on integrable functions. -/
def coeff (L : Length)
    (f : {f : Circle L → ℂ // Integrable f (arclength L)}) (k : ℤ) : ℂ := by
  haveI : Fact (0 < L.val) := ⟨L.property⟩
  exact fourierCoeff f.val k

end Riesz1

end
end
