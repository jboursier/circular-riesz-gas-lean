/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Frozen.Variance
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# The variance of a square-integrable function as a real integral

The variance `Riesz1.variance` is the lower integral of `ofReal ((F - ∫F)^2)`. For a
square-integrable `F` on a probability space it equals `ENNReal.ofReal` of the real integral
`∫ (F - ∫F)^2`. This bridge lets real-valued estimates of the variance pass to `Riesz1.variance`.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Riesz1

/-- For a square-integrable `F` on a probability space, the variance is `ofReal` of the
real centered integral. -/
theorem variance_eq_ofReal_integral_sq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (F : Ω → ℝ) (hF : MemLp F 2 μ) :
    variance μ F (hF.integrable one_le_two) =
      ENNReal.ofReal (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) := by
  have hm : MemLp (fun x => F x - ∫ y, F y ∂μ) 2 μ := hF.sub (memLp_const (∫ y, F y ∂μ))
  rw [variance, ofReal_integral_eq_lintegral_ofReal hm.integrable_sq
    (ae_of_all _ fun x => sq_nonneg _)]

end Riesz1

end
