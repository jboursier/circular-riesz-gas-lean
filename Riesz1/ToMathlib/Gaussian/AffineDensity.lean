/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Gaussian densities with affine perturbations

The affine lower bounds from convex regularization give integrable Gaussian majorants.
Normalization below is used only after proving a strictly positive finite integral.
-/

public section

open MeasureTheory Set Filter
open scoped InnerProductSpace

namespace Riesz1.Gaussian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A Gaussian times the exponential of any affine function is integrable. -/
lemma integrable_exp_quadratic_affine {w : ℝ} (hw : 0 < w) (a : E) (b : ℝ) :
    Integrable (fun x : E => Real.exp (-((2*w)⁻¹ * ‖x‖^2 + ⟪a,x⟫_ℝ + b))) volume := by
  have hi := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := E) (b := ((2*w)⁻¹ : ℝ))
      (by simpa using inv_pos.mpr (mul_pos (by norm_num : (0 : ℝ) < 2) hw)) (-1) a).re
  have hi' : Integrable (fun x : E => Real.exp (-((2*w)⁻¹ * ‖x‖^2) - ⟪a,x⟫_ℝ)) volume := by
    convert hi using 1
    funext x
    have he : -((↑((2*w)⁻¹) : ℂ) * ↑‖x‖ ^ 2) + -1 * ↑⟪a,x⟫_ℝ =
        ↑(-((2*w)⁻¹ * ‖x‖^2) - ⟪a,x⟫_ℝ) := by push_cast; ring
    rw [neg_mul, he]
    change Real.exp _ = (Complex.exp _).re
    rw [← Complex.ofReal_exp, Complex.ofReal_re]
  convert hi'.mul_const (Real.exp (-b)) using 1
  funext x
  rw [← Real.exp_add]
  congr 1
  ring

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Normalizing a nonnegative integrable real density of positive mass gives a probability. -/
lemma isProbabilityMeasure_normalized_density {μ : Measure E} {p : E → ℝ}
    (hi : Integrable p μ) (hp : ∀ x, 0 ≤ p x) (hZ : 0 < ∫ x, p x ∂μ) :
    IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (p x / ∫ y, p y ∂μ))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hi.div_const _)
      (Eventually.of_forall (fun x => div_nonneg (hp x) hZ.le)), integral_div,
    div_self hZ.ne', ENNReal.ofReal_one]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- A probability proportional to a nonnegative integrable density is its normalized law. -/
lemma eq_normalized_density_of_probability {ν μ : Measure E} [IsProbabilityMeasure ν]
    {p : E → ℝ} (hi : Integrable p μ) (hp : ∀ x, 0 ≤ p x) (hZ : 0 < ∫ x, p x ∂μ)
    {c : ℝ} (hc : 0 < c)
    (he : ν = μ.withDensity (fun x => ENNReal.ofReal (c * p x))) :
    ν = μ.withDensity (fun x => ENNReal.ofReal (p x / ∫ y, p y ∂μ)) := by
  have hm : ENNReal.ofReal (c * ∫ x, p x ∂μ) = 1 := by
    rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal (hi.const_mul c)
      (Eventually.of_forall (fun x => mul_nonneg hc.le (hp x)))]
    have h := measure_univ (μ := ν)
    rw [he, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
    exact h
  have hm' : c * ∫ x, p x ∂μ = 1 := by
    have h := congrArg ENNReal.toReal hm
    simpa only [ENNReal.toReal_ofReal (mul_nonneg hc.le (integral_nonneg hp)),
      ENNReal.toReal_one] using h
  have hc' : c = 1 / ∫ x, p x ∂μ := (eq_div_iff hZ.ne').mpr hm'
  rw [he]
  congr 1
  funext x
  rw [hc']
  congr 1
  ring

end Riesz1.Gaussian
