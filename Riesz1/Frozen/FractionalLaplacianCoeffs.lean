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

/-!
# Fractional Laplacian coefficients: `Riesz1.fractionalLaplacianCoeffs`

Fourier multiplier for the fractional Laplacian, including inverse powers on
mean-zero coefficients.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Fourier multiplier for the fractional Laplacian, including inverse powers on
mean-zero coefficients. -/
def fractionalLaplacianCoeffs (L : Length) (gamma : ℝ) (a : ℤ → ℂ) (k : ℤ) : ℂ :=
  if k = 0 then 0 else (|2 * Real.pi * (k : ℝ) / L.val| ^ (2 * gamma) : ℝ) * a k


end Riesz1

end
end
