/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.KernelSplitDerivative

/-!
# Local differentiation of the far kernel

The derivative and bounds are required only at the displacements reached from a
neighborhood of the evaluation point and the integration set. This allows a
periodic kernel with singularities outside that range, as needed in
Lemma 5.3.
-/

public section

open MeasureTheory Set Filter Topology Metric

namespace Riesz1

/-- Differentiate a convolution using hypotheses local to the displacement range.
The kernel need only be measurable globally. -/
theorem hasDerivAt_integral_mul_sub_local {S : Set ℝ} (hS : MeasurableSet S)
    {q K : ℝ → ℝ} {x₀ ε N M : ℝ} (hε : 0 < ε)
    (hq : IntegrableOn q S) (hKm : Measurable K)
    (hKN : ∀ y ∈ S, |K (x₀ - y)| ≤ N)
    (hgood : ∀ x ∈ ball x₀ ε, ∀ y ∈ S,
      DifferentiableAt ℝ K (x - y) ∧ |deriv K (x - y)| ≤ M) :
    HasDerivAt (fun x => ∫ y in S, q y * K (x - y))
      (∫ y in S, q y * deriv K (x₀ - y)) x₀ := by
  have hmeas (x : ℝ) :
      AEStronglyMeasurable (fun y => q y * K (x - y)) (volume.restrict S) :=
    hq.aestronglyMeasurable.mul
      ((hKm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
  have hint : IntegrableOn (fun y => q y * K (x₀ - y)) S := by
    refine (hq.norm.const_mul N).mono' (hmeas x₀) ?_
    filter_upwards [ae_restrict_mem hS] with y hy
    calc ‖q y * K (x₀ - y)‖ = ‖q y‖ * |K (x₀ - y)| := by
          simp only [norm_mul, Real.norm_eq_abs]
      _ ≤ ‖q y‖ * N := mul_le_mul_of_nonneg_left (hKN y hy) (norm_nonneg _)
      _ = N * ‖q y‖ := mul_comm _ _
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict S)
    (F := fun x y => q y * K (x - y))
    (F' := fun x y => q y * deriv K (x - y))
    (x₀ := x₀) (bound := fun y => M * ‖q y‖) (s := ball x₀ ε)
    (ball_mem_nhds x₀ hε) (Eventually.of_forall hmeas) hint ?_ ?_
    (hq.norm.const_mul M) ?_).2
  · exact hq.aestronglyMeasurable.mul
      (((measurable_deriv K).comp
        (measurable_const.sub measurable_id)).aestronglyMeasurable)
  · filter_upwards [ae_restrict_mem hS] with y hy
    intro x hx
    calc ‖q y * deriv K (x - y)‖ = ‖q y‖ * |deriv K (x - y)| := by
          simp only [norm_mul, Real.norm_eq_abs]
      _ ≤ ‖q y‖ * M :=
        mul_le_mul_of_nonneg_left (hgood x hx y hy).2 (norm_nonneg _)
      _ = M * ‖q y‖ := mul_comm _ _
  · filter_upwards [ae_restrict_mem hS] with y hy
    intro x hx
    exact HasDerivAt.const_mul (q y)
      (HasDerivAt.comp_sub_const x y (hgood x hx y hy).1.hasDerivAt)

end Riesz1
