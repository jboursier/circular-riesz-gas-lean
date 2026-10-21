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
public import Riesz1.Frozen.Coeff
public import Riesz1.Frozen.HolderBound
public import Riesz1.Frozen.ComplexL2Integrable

/-!
# Primitive regularity: `Riesz1.PrimitiveRegularity`

(A1) of Assumption 1.1 in the distributional (Fourier coefficient) sense.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- (A1) of Assumption 1.1 in the distributional (Fourier coefficient) sense. -/
def PrimitiveRegularity (L : Length) (eta s B : ℝ) (f : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)}) : Prop :=
  ∃ Xi : {g : Circle L → ℝ // MemLp (fun x => (g x : ℂ)) 2 (arclength L)},
    HolderBound L (1 - s + eta) B Xi.val ∧
    ∀ k : ℤ, k ≠ 0 →
      (2 * Real.pi * Complex.I * (k : ℂ) / L.val) * coeff L ⟨(fun x => (Xi.val x : ℂ)), complexL2Integrable L _ Xi.property⟩ k =
        coeff L ⟨(fun x => (f.val x : ℂ)), complexL2Integrable L _ f.property⟩ k


end Riesz1

end
end
