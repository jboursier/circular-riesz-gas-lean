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
# Integrability of complex L² functions: `Riesz1.complexL2Integrable`

Complex L² representatives are integrable on a finite circle.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Complex L² representatives are integrable on a finite circle. -/
theorem complexL2Integrable (L : Length) (f : Circle L → ℂ)
    (hf : MemLp f 2 (arclength L)) : Integrable f (arclength L) := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  change Integrable f volume
  exact (show MemLp f 2 volume from hf).integrable (by norm_num)

end Riesz1

end
end
