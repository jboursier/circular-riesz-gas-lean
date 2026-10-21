/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.Poincare.Product

/-! # Integrating the slice bounds in variance tensorization

An internal product-measure estimate, separating the analytic slice
inequalities from the integration step.
-/

public section

noncomputable section

open MeasureTheory Filter

namespace Riesz1.Poincare

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

theorem product_energy_bound {f R T : α × β → ℝ}
    (hf : StronglyMeasurable f) {C : ℝ} (hC : ∀ p, ‖f p‖ ≤ C)
    (hR : Integrable R (μ.prod ν)) (hT : Integrable T (μ.prod ν)) {A B : ℝ}
    (hfirst : ∀ᵐ y ∂ν, (∫ x, (f (x, y) - ∫ z, f (z, y) ∂μ) ^ 2 ∂μ) ≤
      A * ∫ x, R (x, y) ∂μ)
    (hsecond : ∀ᵐ x ∂μ, (∫ y, (f (x, y) - ∫ z, f (x, z) ∂ν) ^ 2 ∂ν) ≤
      B * ∫ y, T (x, y) ∂ν) :
    (∫ p, (f p - ∫ q, f q ∂μ.prod ν) ^ 2 ∂μ.prod ν) ≤
      B * ∫ p, T p ∂μ.prod ν + A * ∫ p, R p ∂μ.prod ν := by
  have hF : MemLp f 2 (μ.prod ν) :=
    MemLp.of_bound hf.aestronglyMeasurable C (Eventually.of_forall hC)
  have hleft := poincare_memLp_mean μ ν hf hC
  have hright := poincare_memLp_mean ν μ (hf.comp_measurable measurable_swap)
    (fun p => hC p.swap)
  have hvl : Integrable (fun x => ∫ y, (f (x, y) - ∫ z, f (x, z) ∂ν) ^ 2 ∂ν) μ :=
    (hF.sub (hleft.comp_fst ν)).integrable_sq.integral_prod_left
  have hvr : Integrable (fun y => ∫ x, (f (x, y) - ∫ z, f (z, y) ∂μ) ^ 2 ∂μ) ν :=
    (hF.sub (hright.comp_snd μ)).integrable_sq.integral_prod_right
  have hl := integral_mono_ae hvl (hT.integral_prod_left.const_mul B) hsecond
  have hr := integral_mono_ae hvr (hR.integral_prod_right.const_mul A) hfirst
  rw [integral_const_mul, ← integral_prod _ hT] at hl
  rw [integral_const_mul, ← integral_integral_swap (f := fun x y => R (x, y)) hR,
    ← integral_prod _ hR] at hr
  exact (integral_sub_mean_sq_prod_le μ ν hf hC).trans (add_le_add hl hr)

end Riesz1.Poincare

end
