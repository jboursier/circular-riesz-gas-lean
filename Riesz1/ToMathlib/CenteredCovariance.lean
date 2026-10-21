/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Covariance of a centred factor on a probability space

For integrable `f, g` on a probability space, the centring of the first factor gives the
covariance `∫ (f - ∫f)(g - ∫g) = ∫ (f - ∫f) g`. This is the form of the covariance identity used
for the anchored law in Remark 3.2.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Riesz1

/-- The integral of a centred product on a probability space, with the centring of the first
factor only. This is the covariance identity in the form used below. -/
theorem integral_centered_mul {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : Integrable (fun y => f y * g y) μ) :
    ∫ y, (f y - ∫ x, f x ∂μ) * (g y - ∫ x, g x ∂μ) ∂μ =
      ∫ y, (f y - ∫ x, f x ∂μ) * g y ∂μ := by
  have hzero : ∫ y, (f y - ∫ x, f x ∂μ) ∂μ = 0 := by
    rw [integral_sub hf (integrable_const _), integral_const]
    simp
  have hfg' : Integrable (fun y => (f y - ∫ x, f x ∂μ) * g y) μ := by
    have h := hfg.sub (hg.const_mul (∫ x, f x ∂μ))
    convert h using 1
    funext y
    simp only [Pi.sub_apply]
    ring
  have key : (fun y => (f y - ∫ x, f x ∂μ) * (g y - ∫ x, g x ∂μ)) =
      fun y => (f y - ∫ x, f x ∂μ) * g y - (∫ x, g x ∂μ) * (f y - ∫ x, f x ∂μ) := by
    funext y
    ring
  have hint2 : Integrable (fun y => (∫ x, g x ∂μ) * (f y - ∫ x, f x ∂μ)) μ :=
    (hf.sub (integrable_const _)).const_mul _
  rw [key, integral_sub hfg' hint2, integral_const_mul, hzero, mul_zero, sub_zero]

end Riesz1

end
