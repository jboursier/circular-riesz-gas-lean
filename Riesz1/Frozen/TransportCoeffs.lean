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
public import Riesz1.Frozen.Length
public import Riesz1.Frozen.Circle
public import Riesz1.Frozen.Arclength
public import Riesz1.Frozen.Coeff
public import Riesz1.Frozen.RieszConstant
public import Riesz1.Frozen.ComplexL2Integrable

/-!
# Transport coefficients: `Riesz1.transportCoeffs`

Mean-zero transport coefficients, hence the distribution uniquely.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Mean-zero transport coefficients, hence the distribution uniquely. -/
def transportCoeffs (P : Parameters) (L : Length) (f : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)}) (k : ℤ) : ℂ :=
  if k = 0 then 0 else
    -((|2 * Real.pi * (k : ℝ) / L.val| ^ (1 - P.val.2) : ℝ) : ℂ) /
      ((2 * P.val.1 * rieszConstant (parametersExponent P) : ℝ) * (2 * Real.pi * Complex.I * (k : ℂ) / L.val)) *
        coeff L ⟨(fun x => (f.val x : ℂ)), complexL2Integrable L _ f.property⟩ k


end Riesz1

end
end
