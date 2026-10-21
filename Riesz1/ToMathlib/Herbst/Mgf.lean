/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Exponential moments of bounded functions

For a bounded continuous function `F` on a normed space `E` with a probability measure `μ`,
the functions `r ↦ ∫ exp (r F) dμ` are finite, positive and differentiable in `r`, with
derivative `∫ F exp (r F) dμ`. The lemmas here prepare the Herbst argument of
`Riesz1.Herbst`, which applies them to the log-Sobolev inequality.
-/

public section

open MeasureTheory Filter Topology Set
namespace Riesz1

/-- The bound `|F x| ≤ C` gives `exp (r F x) ≤ exp (|r| C)` for every real `r`. -/
lemma herbst_exp_le {E : Type*} {F : E → ℝ} {C : ℝ} (hC : ∀ x, |F x| ≤ C) (r : ℝ) (x : E) :
    Real.exp (r * F x) ≤ Real.exp (|r| * C) := by
  refine Real.exp_le_exp.mpr ?_
  calc r * F x ≤ |r * F x| := le_abs_self _
    _ = |r| * |F x| := abs_mul _ _
    _ ≤ |r| * C := mul_le_mul_of_nonneg_left (hC x) (abs_nonneg _)

/-- A bounded continuous real function is integrable for every finite measure. -/
lemma herbst_integrable_of_bounded {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] {μ : Measure E} [IsFiniteMeasure μ] {f : E → ℝ}
    (hf : Continuous f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)

/-- For a bounded continuous `F`, the function `x ↦ exp (r F x)` is integrable. -/
lemma herbst_integrable_exp {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] {μ : Measure E} [IsFiniteMeasure μ] {F : E → ℝ}
    (hF : Continuous F) {C : ℝ} (hC : ∀ x, |F x| ≤ C) (r : ℝ) :
    Integrable (fun x => Real.exp (r * F x)) μ :=
  herbst_integrable_of_bounded (C := Real.exp (|r| * C))
    (Real.continuous_exp.comp (continuous_const.mul hF))
    (fun x => by rw [abs_of_pos (Real.exp_pos _)]; exact herbst_exp_le hC r x)

/-- The moment generating function `r ↦ ∫ exp (r F) dμ` of a bounded continuous `F` is
differentiable with derivative `∫ F exp (s F) dμ` at every point `s`. -/
lemma herbst_hasDerivAt_mgf {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] {μ : Measure E} [IsFiniteMeasure μ] {F : E → ℝ}
    (hF : Continuous F) {C : ℝ} (hC : ∀ x, |F x| ≤ C) (s : ℝ) :
    HasDerivAt (fun r : ℝ => ∫ x, Real.exp (r * F x) ∂μ)
      (∫ x, F x * Real.exp (s * F x) ∂μ) s := by
  have hmeas : ∀ r : ℝ, Continuous (fun x => Real.exp (r * F x)) := fun r =>
    Real.continuous_exp.comp (continuous_const.mul hF)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun r x => Real.exp (r * F x)) (F' := fun r x => F x * Real.exp (r * F x))
    (x₀ := s) (s := Metric.ball s 1) (bound := fun _ => C * Real.exp ((|s| + 1) * C))
    (Metric.ball_mem_nhds s one_pos)
    (Eventually.of_forall fun r => (hmeas r).aestronglyMeasurable)
    (herbst_integrable_exp hF hC s)
    (hF.mul (hmeas s)).aestronglyMeasurable ?_ (integrable_const _) ?_).2
  · refine Eventually.of_forall fun a r hr => ?_
    have hr' : |r| ≤ |s| + 1 := by
      have h1 : dist r s < 1 := Metric.mem_ball.mp hr
      rw [Real.dist_eq] at h1
      have h2 := abs_sub_abs_le_abs_sub r s
      linarith
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC a)
    have hexp : Real.exp (r * F a) ≤ Real.exp ((|s| + 1) * C) :=
      (herbst_exp_le hC r a).trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hr' hC0))
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (hC a) hexp (Real.exp_pos _).le hC0
  · refine Eventually.of_forall fun a r _ => ?_
    have h := (hasDerivAt_mul_const (x := r) (F a)).exp
    convert h using 1
    ring

/-- The moment generating function of a bounded continuous function is positive for a
probability measure. -/
lemma herbst_integral_exp_pos {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ] {F : E → ℝ}
    (hF : Continuous F) {C : ℝ} (hC : ∀ x, |F x| ≤ C) (r : ℝ) :
    0 < ∫ x, Real.exp (r * F x) ∂μ := by
  rw [integral_pos_iff_support_of_nonneg (fun x => (Real.exp_pos _).le)
    (herbst_integrable_exp hF hC r)]
  have hsupp : Function.support (fun x => Real.exp (r * F x)) = univ := by
    ext x
    simp [Real.exp_ne_zero]
  rw [hsupp, measure_univ]
  exact one_pos

/-- The derivative of `x ↦ exp (c F x)` at a point where `F` is differentiable. -/
lemma herbst_fderiv_exp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : E → ℝ}
    {x : E} (hF : DifferentiableAt ℝ F x) (c : ℝ) :
    fderiv ℝ (fun y => Real.exp (c * F y)) x = Real.exp (c * F x) • (c • fderiv ℝ F x) := by
  have hexp : HasDerivAt Real.exp (Real.exp (c * F x)) (c * F x) := Real.hasDerivAt_exp _
  have hlin : HasFDerivAt (fun y => c * F y) (c • fderiv ℝ F x) x := hF.hasFDerivAt.const_mul c
  have h : HasFDerivAt (Real.exp ∘ fun y => c * F y)
      (Real.exp (c * F x) • (c • fderiv ℝ F x)) x :=
    HasDerivAt.comp_hasFDerivAt x hexp hlin
  exact h.fderiv

/-- The norm of the derivative of `x ↦ exp (c F x)`, written as a product of the exponential,
the scalar `|c|` and the norm of the derivative of `F`. -/
lemma herbst_norm_fderiv_exp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : E → ℝ}
    {x : E} (hF : DifferentiableAt ℝ F x) (c : ℝ) :
    ‖fderiv ℝ (fun y => Real.exp (c * F y)) x‖
      = Real.exp (c * F x) * (|c| * ‖fderiv ℝ F x‖) := by
  rw [herbst_fderiv_exp hF c, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

end Riesz1
