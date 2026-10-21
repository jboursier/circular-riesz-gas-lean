/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Differentiating convolutions after splitting a singular kernel

Let `q` be an integrable function and `K` a kernel. The convolution `x ↦ ∫ q(y) K(x - y) dy`
over a set `S` is differentiated under the integral sign in two situations.

* `hasDerivAt_integral_mul_sub`: the kernel `K` is differentiable with a bounded derivative, so
  the derivative falls on the kernel. The derivative is `∫ q(y) K'(x - y) dy`.
* `hasDerivAt_integral_comp_sub_mul`: the kernel `K` is integrable on a set `T` of displacements
  `t`, and the derivative falls on `q` at the points `x - t`. The derivative is
  `∫ q'(x - t) K(t) dt`, valid when `q` is differentiable with bounded derivative near `x - t`.

These two identities are the analytic step that avoids principal values in the derivative of
`P_L * q` in Lemma 5.3: the singular kernel `P_L'` is never integrated against `q`.
The kernel is split as `P_L = P_near + P_far`, where `P_near` is supported in a small interval and
integrable, and `P_far` is smooth with bounded derivative.
-/

public section

open MeasureTheory Set Filter Topology Metric

namespace Riesz1

/-- **Derivative falling on a bounded kernel.** Let `q` be integrable on `S`, and let `K` be a
bounded differentiable kernel whose derivative is bounded. Then the convolution
`x ↦ ∫_S q(y) K(x - y) dy` has the derivative `∫_S q(y) K'(x - y) dy` at every point. -/
theorem hasDerivAt_integral_mul_sub {S : Set ℝ} {q K : ℝ → ℝ} {N M : ℝ}
    (hq : IntegrableOn q S) (hK : Differentiable ℝ K) (hKN : ∀ t, |K t| ≤ N)
    (hKM : ∀ t, |deriv K t| ≤ M) (x : ℝ) :
    HasDerivAt (fun z => ∫ y in S, q y * K (z - y))
      (∫ y in S, q y * deriv K (x - y)) x := by
  have hKc : Continuous K := hK.continuous
  have hKd : Measurable (deriv K) := measurable_deriv K
  have hmeas : ∀ z : ℝ, AEStronglyMeasurable (fun y => q y * K (z - y)) (volume.restrict S) :=
    fun z => hq.aestronglyMeasurable.mul
      ((hKc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
  have hint : ∀ z : ℝ, Integrable (fun y => q y * K (z - y)) (volume.restrict S) := by
    intro z
    refine (hq.norm.const_mul N).mono' (hmeas z) (Filter.Eventually.of_forall fun y => ?_)
    calc ‖q y * K (z - y)‖ = ‖q y‖ * |K (z - y)| := by simp only [norm_mul, Real.norm_eq_abs]
      _ ≤ ‖q y‖ * N := mul_le_mul_of_nonneg_left (hKN _) (norm_nonneg _)
      _ = N * ‖q y‖ := mul_comm _ _
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict S)
    (F := fun z y => q y * K (z - y)) (F' := fun z y => q y * deriv K (z - y))
    (x₀ := x) (bound := fun y => M * ‖q y‖) (s := Metric.ball x 1) (Metric.ball_mem_nhds x one_pos)
    (Filter.Eventually.of_forall fun z => hmeas z) (hint x)
    ?_ ?_ (hq.norm.const_mul M) ?_).2
  · exact (hq.aestronglyMeasurable.mul
      ((hKd.comp (measurable_const.sub measurable_id)).aestronglyMeasurable))
  · refine Filter.Eventually.of_forall fun y z _ => ?_
    calc ‖q y * deriv K (z - y)‖ = ‖q y‖ * |deriv K (z - y)| := by simp only [norm_mul, Real.norm_eq_abs]
      _ ≤ ‖q y‖ * M := mul_le_mul_of_nonneg_left (hKM _) (norm_nonneg _)
      _ = M * ‖q y‖ := mul_comm _ _
  · refine Filter.Eventually.of_forall fun y z _ => ?_
    exact HasDerivAt.const_mul (q y) (HasDerivAt.comp_sub_const z y (hK (z - y)).hasDerivAt)

/-- **Derivative falling on the transported function.** Let `K` be integrable on a measurable set
`T` of displacements, and let `q` be measurable and differentiable at every point `x - t` with
`x` in a ball around `x₀` and `t ∈ T`, with `|q'(x - t)| ≤ M` there. If the convolution integrand
is integrable at `x₀`, then `x ↦ ∫_T q(x - t) K(t) dt` has the derivative
`∫_T q'(x₀ - t) K(t) dt` at `x₀`. -/
theorem hasDerivAt_integral_comp_sub_mul {T : Set ℝ} (hT : MeasurableSet T) {q K : ℝ → ℝ}
    {x₀ ε M : ℝ} (hε : 0 < ε) (hqm : Measurable q) (hKint : IntegrableOn K T)
    (hF : IntegrableOn (fun t => q (x₀ - t) * K t) T)
    (hgood : ∀ x ∈ ball x₀ ε, ∀ t ∈ T, DifferentiableAt ℝ q (x - t) ∧ |deriv q (x - t)| ≤ M) :
    HasDerivAt (fun x => ∫ t in T, q (x - t) * K t) (∫ t in T, deriv q (x₀ - t) * K t) x₀ := by
  have hae : ∀ᵐ t ∂(volume.restrict T), t ∈ T := ae_restrict_mem hT
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict T)
    (F := fun x t => q (x - t) * K t) (F' := fun x t => deriv q (x - t) * K t)
    (x₀ := x₀) (bound := fun t => M * ‖K t‖) (s := ball x₀ ε) (Metric.ball_mem_nhds x₀ hε)
    (Filter.Eventually.of_forall fun x =>
      (hqm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable.mul
        hKint.aestronglyMeasurable)
    hF ?_ ?_ (hKint.norm.const_mul M) ?_).2
  · exact ((measurable_deriv q).comp (measurable_const.sub measurable_id)).aestronglyMeasurable.mul
      hKint.aestronglyMeasurable
  · filter_upwards [hae] with t ht
    intro x hx
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (by rw [Real.norm_eq_abs]; exact (hgood x hx t ht).2)
      (norm_nonneg _)
  · filter_upwards [hae] with t ht
    intro x hx
    exact HasDerivAt.mul_const (HasDerivAt.comp_sub_const x t (hgood x hx t ht).1.hasDerivAt) (K t)

end Riesz1
