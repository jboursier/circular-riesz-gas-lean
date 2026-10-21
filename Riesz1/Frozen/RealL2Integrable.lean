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
# Real L² integrability: `Riesz1.realL2Integrable`

Real L² representatives have a finite first moment on the circle.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Real L² representatives have a finite first moment on the circle. -/
theorem realL2Integrable (L : Length) (f : Circle L → ℝ)
    (hf : MemLp (fun x => (f x : ℂ)) 2 (arclength L)) : Integrable f (arclength L) := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  have hf' : MemLp f 2 (arclength L) := hf.re
  have : IsFiniteMeasure (arclength L) := by unfold arclength; infer_instance
  exact hf'.integrable (by norm_num)

end Riesz1

end
end
