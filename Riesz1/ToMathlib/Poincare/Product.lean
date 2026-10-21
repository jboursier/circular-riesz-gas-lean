/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.WeightedSobolev.L2Facts
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Variance tensorization for two probability measures

For a bounded measurable function on a product, its variance is at most
the sum of its averaged slice variances. This is the tensorization step.
No derivative of a conditional mean is needed.
-/

public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Averaging a bounded jointly measurable real function gives an `L²` function. -/
theorem poincare_memLp_mean {f : α × β → ℝ} (hf : StronglyMeasurable f) {C : ℝ}
    (hC : ∀ p, ‖f p‖ ≤ C) : MemLp (fun x => ∫ y, f (x, y) ∂ν) 2 μ := by
  refine MemLp.of_bound hf.integral_prod_right'.aestronglyMeasurable C ?_
  filter_upwards with x
  simpa using norm_integral_le_of_norm_le_const
    (μ := ν) (Filter.Eventually.of_forall fun y => hC (x, y))

/-- The conditional-variance identity on a product, for bounded measurable tests. -/
theorem integral_sub_mean_sq_prod {f : α × β → ℝ} (hf : StronglyMeasurable f) {C : ℝ}
    (hC : ∀ p, ‖f p‖ ≤ C) :
    (∫ p, (f p - ∫ q, f q ∂μ.prod ν) ^ 2 ∂μ.prod ν) =
      (∫ x, ∫ y, (f (x, y) - ∫ z, f (x, z) ∂ν) ^ 2 ∂ν ∂μ) +
      ∫ x, ((∫ y, f (x, y) ∂ν) - ∫ q, f q ∂μ.prod ν) ^ 2 ∂μ := by
  have hF : MemLp f 2 (μ.prod ν) :=
    MemLp.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
  have hA := poincare_memLp_mean μ ν hf hC
  have hslice (x : α) : MemLp (fun y => f (x, y)) 2 ν :=
    MemLp.of_bound (hf.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      C (Filter.Eventually.of_forall fun y => hC (x, y))
  have hid : (∫ x, ∫ y, (f (x, y) - ∫ z, f (x, z) ∂ν) ^ 2 ∂ν ∂μ) =
      (∫ p, f p ^ 2 ∂μ.prod ν) - ∫ x, (∫ y, f (x, y) ∂ν) ^ 2 ∂μ := by
    simp_rw [WeightedSobolev.integral_sub_mean_sq (hslice _)]
    rw [integral_sub hF.integrable_sq.integral_prod_left hA.integrable_sq,
      ← integral_prod _ hF.integrable_sq]
  rw [hid, WeightedSobolev.integral_sub_mean_sq hF]
  have hm := integral_prod f (hF.integrable one_le_two)
  rw [hm, WeightedSobolev.integral_sub_mean_sq hA]
  ring

/-- Variance tensorization: the variance on a product is bounded by the
sum of the mean variances in its two factors. -/
theorem integral_sub_mean_sq_prod_le {f : α × β → ℝ} (hf : StronglyMeasurable f) {C : ℝ}
    (hC : ∀ p, ‖f p‖ ≤ C) :
    (∫ p, (f p - ∫ q, f q ∂μ.prod ν) ^ 2 ∂μ.prod ν) ≤
      (∫ x, ∫ y, (f (x, y) - ∫ z, f (x, z) ∂ν) ^ 2 ∂ν ∂μ) +
      ∫ y, ∫ x, (f (x, y) - ∫ z, f (z, y) ∂μ) ^ 2 ∂μ ∂ν := by
  have hF : MemLp f 2 (μ.prod ν) :=
    MemLp.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
  have hA := poincare_memLp_mean μ ν hf hC
  let B : β → ℝ := fun y => ∫ x, f (x, y) ∂μ
  have hB : MemLp B 2 ν := poincare_memLp_mean ν μ
    (hf.comp_measurable measurable_swap) (fun p => hC p.swap)
  have hK : MemLp (fun p : α × β => f p - B p.2) 2 (μ.prod ν) :=
    hF.sub (hB.comp_snd μ)
  have hslice (x : α) : MemLp (fun y => f (x, y) - B y) 2 ν :=
    (MemLp.of_bound
      (hf.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      C (Filter.Eventually.of_forall fun y => hC (x, y))).sub hB
  have hmean : ∫ y, B y ∂ν = ∫ q, f q ∂μ.prod ν :=
    (integral_integral_swap (f := fun x y => f (x, y)) (hF.integrable one_le_two)).symm.trans
      (integral_prod f (hF.integrable one_le_two)).symm
  have hpt (x : α) :
      ((∫ y, f (x, y) ∂ν) - ∫ q, f q ∂μ.prod ν) ^ 2 ≤
        ∫ y, (f (x, y) - B y) ^ 2 ∂ν := by
    have hnonneg := integral_nonneg (μ := ν) (fun y =>
      sq_nonneg (f (x, y) - B y - ∫ z, (f (x, z) - B z) ∂ν))
    rw [WeightedSobolev.integral_sub_mean_sq (hslice x)] at hnonneg
    have hfx : Integrable (fun y => f (x, y)) ν :=
      ((hslice x).add hB).integrable one_le_two |>.congr
        (Filter.Eventually.of_forall fun y => sub_add_cancel _ _)
    rw [integral_sub hfx (hB.integrable one_le_two), hmean] at hnonneg
    linarith
  have hi : Integrable (fun x => ((∫ y, f (x, y) ∂ν) -
      ∫ q, f q ∂μ.prod ν) ^ 2) μ := (hA.sub (memLp_const _)).integrable_sq
  rw [integral_sub_mean_sq_prod μ ν hf hC]
  apply add_le_add_right
  have hle := integral_mono_ae hi hK.integrable_sq.integral_prod_left
    (Filter.Eventually.of_forall hpt)
  have hswap := integral_integral_swap (f := fun x y => (f (x, y) - B y) ^ 2) hK.integrable_sq
  exact hle.trans_eq hswap

end Riesz1

end
