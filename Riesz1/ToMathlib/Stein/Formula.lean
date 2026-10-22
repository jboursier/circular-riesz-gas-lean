/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.Stein.Gaussian
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The integrating-factor solution of the Gaussian Stein equation

The solution is the Gaussian integrating factor times the integral of the centered test function
from minus infinity. Continuous tests with at most linear growth give differentiable solutions.
Every bounded differentiable solution agrees with this formula.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Set Filter Topology

namespace Riesz1

/-- The integrating-factor solution for a Gaussian of standard deviation `σ`. -/
noncomputable def steinSolution (σ : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (σ ^ 2)⁻¹ * rexp (x ^ 2 / (2 * σ ^ 2)) *
    ∫ y in Iic x, rexp (-(y ^ 2) / (2 * σ ^ 2)) *
      (f y - ∫ z, f (σ * z) ∂(gaussianReal 0 1))

/-- The solution written with expectation under the Gaussian law of variance `σ²`. -/
lemma steinSolution_eq_integratingFactor (σ : ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    steinSolution σ f = fun x =>
      (σ ^ 2)⁻¹ * rexp (x ^ 2 / (2 * σ ^ 2)) *
        ∫ y in Iic x, rexp (-(y ^ 2) / (2 * σ ^ 2)) *
          (f y - ∫ z, f z ∂(gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩)) := by
  unfold steinSolution
  rw [stein_integral_gaussian_scale σ hf]

namespace Internal

/-- The integrating-factor solution is homogeneous in its test function. -/
lemma stein_solution_const_mul (σ a : ℝ) (f : ℝ → ℝ) :
    steinSolution σ (fun x => a * f x) = fun x => a * steinSolution σ f x := by
  funext x
  unfold steinSolution
  simp only [integral_const_mul]
  have he : (fun y => rexp (-(y ^ 2) / (2 * σ ^ 2)) *
      (a * f y - a * ∫ z, f (σ * z) ∂(gaussianReal 0 1))) =
      fun y => a * (rexp (-(y ^ 2) / (2 * σ ^ 2)) *
        (f y - ∫ z, f (σ * z) ∂(gaussianReal 0 1))) := by
    funext y
    ring
  rw [he, integral_const_mul]
  ring

/-- Gaussian decay makes a continuous function of at most linear growth integrable. -/
lemma stein_integrable_weight {σ : ℝ} (hσ : 0 < σ) {f : ℝ → ℝ} (hf : Continuous f)
    {A B : ℝ} (hb : ∀ y, |f y| ≤ A + B * |y|) :
    Integrable (fun y => rexp (-(y ^ 2) / (2 * σ ^ 2)) * f y) := by
  have hp : 0 < (2 * σ ^ 2)⁻¹ := by positivity
  have he : Integrable (fun y : ℝ => rexp (-(y ^ 2) / (2 * σ ^ 2))) := by
    convert integrable_exp_neg_mul_sq hp using 1
    ext y
    congr 1
    ring
  have hy : Integrable (fun y : ℝ => |y| * rexp (-(y ^ 2) / (2 * σ ^ 2))) := by
    convert (integrable_mul_exp_neg_mul_sq hp).norm using 1
    ext y
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    congr 2
    ring
  refine ((he.const_mul A).add (hy.const_mul B)).mono' (by fun_prop) ?_
  filter_upwards [] with y
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc rexp (-(y ^ 2) / (2 * σ ^ 2)) * |f y|
      ≤ rexp (-(y ^ 2) / (2 * σ ^ 2)) * (A + B * |y|) :=
        mul_le_mul_of_nonneg_left (hb y) (Real.exp_nonneg _)
    _ = A * rexp (-(y ^ 2) / (2 * σ ^ 2)) +
        B * (|y| * rexp (-(y ^ 2) / (2 * σ ^ 2))) := by ring

/-- Differentiating an integral with a variable upper limit on the whole real line. -/
lemma stein_hasDerivAt_integral_Iic {g : ℝ → ℝ} (hg : Continuous g)
    (hi : Integrable g) (x : ℝ) :
    HasDerivAt (fun x => ∫ y in Iic x, g y) (g x) x := by
  have he : (fun x => ∫ y in Iic x, g y) =
      fun x => (∫ y in Iic (0 : ℝ), g y) + ∫ y in (0 : ℝ)..x, g y := by
    funext y
    have h := intervalIntegral.integral_Iic_sub_Iic
      (hi.integrableOn (s := Iic 0)) (hi.integrableOn (s := Iic y))
    linarith
  rw [he]
  exact (intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable 0 x)
    hg.stronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt).const_add _

/-- The derivative of the integrating-factor solution. -/
lemma stein_hasDerivAt_formula {σ : ℝ} (hσ : 0 < σ) {f : ℝ → ℝ} (hf : Continuous f)
    {A B : ℝ} (hb : ∀ y, |f y| ≤ A + B * |y|) (x : ℝ) :
    HasDerivAt (steinSolution σ f)
      ((x * steinSolution σ f x + f x - ∫ z, f (σ * z) ∂(gaussianReal 0 1)) / σ ^ 2) x := by
  rw [steinSolution_eq_integratingFactor σ hf, stein_integral_gaussian_scale σ hf]
  let c := ∫ z, f (σ * z) ∂(gaussianReal 0 1)
  have hg : Continuous (fun y => rexp (-(y ^ 2) / (2 * σ ^ 2)) * (f y - c)) := by
    fun_prop
  have hi := stein_integrable_weight hσ (hf.sub (continuous_const (y := c)))
    (A := A + |c|) (B := B) (fun y => by
      change |f y - c| ≤ A + |c| + B * |y|
      have := abs_sub (f y) c
      linarith [hb y])
  have hI := stein_hasDerivAt_integral_Iic hg hi x
  have hq : HasDerivAt (fun y : ℝ => y ^ 2 / (2 * σ ^ 2)) (x / σ ^ 2) x := by
    convert (hasDerivAt_pow 2 x).div_const (2 * σ ^ 2) using 1
    ring
  have hd := ((hq.exp.const_mul ((σ ^ 2)⁻¹)).mul hI)
  have hc : rexp (x ^ 2 / (2 * σ ^ 2)) * rexp (-(x ^ 2) / (2 * σ ^ 2)) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 2
    ring
  change HasDerivAt (steinSolution σ f) ((x * steinSolution σ f x + f x - c) / σ ^ 2) x
  refine hd.congr_deriv ?_
  dsimp [steinSolution]
  simp only [← (show c = ∫ z, f (σ * z) ∂(gaussianReal 0 1) from rfl)]
  field_simp at hc ⊢
  linear_combination σ ^ 2 * (f x - c) * hc

/-- Multiplication by the Gaussian integrating factor recovers its forcing term. -/
lemma stein_eq_formula {σ : ℝ} (hσ : 0 < σ) {f u : ℝ → ℝ} (hf : Continuous f)
    {A B : ℝ} (hb : ∀ y, |f y| ≤ A + B * |y|)
    (hu : Differentiable ℝ u) (hub : ∃ C, ∀ x, |u x| ≤ C)
    (he : ∀ x, σ ^ 2 * deriv u x - x * u x =
      f x - ∫ z, f (σ * z) ∂(gaussianReal 0 1)) : u = steinSolution σ f := by
  obtain ⟨C, hC⟩ := hub
  let c := ∫ z, f (σ * z) ∂(gaussianReal 0 1)
  let H := fun x => σ ^ 2 * u x * rexp (-(x ^ 2) / (2 * σ ^ 2))
  have hd : ∀ x, HasDerivAt H (rexp (-(x ^ 2) / (2 * σ ^ 2)) * (f x - c)) x := by
    intro x
    have hq : HasDerivAt (fun y : ℝ => -(y ^ 2) / (2 * σ ^ 2)) (-x / σ ^ 2) x := by
      convert ((hasDerivAt_pow 2 x).neg).div_const (2 * σ ^ 2) using 1
      ring
    have h := ((hu x).hasDerivAt.const_mul (σ ^ 2)).mul hq.exp
    refine h.congr_deriv ?_
    have hx := he x
    change σ ^ 2 * deriv u x - x * u x = f x - c at hx
    field_simp
    nlinarith [hx]
  have hi := stein_integrable_weight hσ (hf.sub (continuous_const (y := c)))
    (A := A + |c|) (B := B) (fun y => by
      change |f y - c| ≤ A + |c| + B * |y|
      linarith [abs_sub (f y) c, hb y])
  have hl : Tendsto (fun x : ℝ => rexp (-(x ^ 2) / (2 * σ ^ 2))) atBot (𝓝 0) := by
    have hsq : Tendsto (fun x : ℝ => x ^ 2) atBot atTop := by
      have h := (tendsto_pow_atTop two_ne_zero (α := ℝ)).comp tendsto_neg_atBot_atTop
      simpa only [Function.comp_def, neg_sq] using h
    have ht := tendsto_neg_atTop_atBot.comp
      (hsq.atTop_div_const (by positivity : 0 < 2 * σ ^ 2))
    simpa only [Function.comp_def, neg_div] using Real.tendsto_exp_atBot.comp ht
  have hH : Tendsto H atBot (𝓝 0) := by
    apply squeeze_zero_norm (fun x => ?_) (by simpa using hl.const_mul (σ ^ 2 * C))
    dsimp [H]
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg σ),
      abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hC x) (sq_nonneg σ))
      (Real.exp_nonneg _)
  funext x
  have hFTC := integral_Iic_of_hasDerivAt_of_tendsto' (a := x) (fun y _ => hd y) hi.integrableOn hH
  rw [sub_zero] at hFTC
  dsimp [steinSolution]
  simp only [← (show c = ∫ z, f (σ * z) ∂(gaussianReal 0 1) from rfl)]
  rw [hFTC]
  dsimp [H]
  have hc : rexp (x ^ 2 / (2 * σ ^ 2)) * rexp (-(x ^ 2) / (2 * σ ^ 2)) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 2
    ring
  field_simp at hc ⊢
  linear_combination -(u x) * hc

end Internal
end Riesz1
