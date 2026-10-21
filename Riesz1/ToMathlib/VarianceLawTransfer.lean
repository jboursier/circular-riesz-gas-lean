/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Riesz1.Frozen.Variance

/-!
# Integrability, variance and laws of real random variables

For a measure `μ` on a measurable space `Ω` and measurable real functions `F`, `G` on `Ω`:

* `integrable_iff_of_map_eq`: `F` is integrable if and only if `G` is, when `F` and `G` have the
  same law.
* `variance_eq_of_map_eq`: the variance `Riesz1.variance` of `F` and of `G` agree in that case.
* `map_eq_of_integral_eq`: for a finite measure, equal integrals of every measurable test function
  of `F` and of `G` force equal laws.

The last fact is the converse direction of the rotation invariance of
`Riesz1.integral_rotate_linearStatistic`, which gives equal integrals of all test functions. The
variance depends only on the law, so equal laws give equal variances.
-/

@[expose] public section

open MeasureTheory Set

namespace Riesz1

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The variance is the lintegral of the squared centred values under the law of the variable. -/
theorem variance_eq_lintegral_map {μ : Measure Ω} {K : Ω → ℝ} (hK : Measurable K)
    (hI : Integrable K μ) :
    variance μ K hI = ∫⁻ y, ENNReal.ofReal ((y - ∫ z, z ∂(μ.map K)) ^ 2) ∂(μ.map K) := by
  have hmean : ∫ z, z ∂(μ.map K) = ∫ x, K x ∂μ :=
    integral_map hK.aemeasurable aestronglyMeasurable_id
  rw [variance, hmean, lintegral_map ?_ hK]
  fun_prop

/-- Integrability of a real function depends only on its law. -/
theorem integrable_iff_of_map_eq {μ : Measure Ω} {F G : Ω → ℝ} (hF : Measurable F)
    (hG : Measurable G) (h : μ.map F = μ.map G) : Integrable F μ ↔ Integrable G μ := by
  have key : ∀ {K : Ω → ℝ}, Measurable K → (Integrable (id : ℝ → ℝ) (μ.map K) ↔ Integrable K μ) :=
    fun hK => integrable_map_measure aestronglyMeasurable_id hK.aemeasurable
  rw [← key hF, ← key hG, h]

/-- The variance depends only on the law of the variable. -/
theorem variance_eq_of_map_eq {μ : Measure Ω} {F G : Ω → ℝ} (hF : Measurable F)
    (hG : Measurable G) (h : μ.map F = μ.map G) (hI : Integrable F μ) (hJ : Integrable G μ) :
    variance μ F hI = variance μ G hJ := by
  rw [variance_eq_lintegral_map hF hI, variance_eq_lintegral_map hG hJ, h]

/-- On a finite measure, equal integrals of every measurable test function `Φ : ℝ → ℝ` of two
real variables give equal laws. The test functions are indicators of the sets `(-∞, a]`. -/
theorem map_eq_of_integral_eq {μ : Measure Ω} [IsFiniteMeasure μ] {F G : Ω → ℝ}
    (hF : Measurable F) (hG : Measurable G)
    (h : ∀ Φ : ℝ → ℝ, Measurable Φ → ∫ x, Φ (F x) ∂μ = ∫ x, Φ (G x) ∂μ) :
    μ.map F = μ.map G := by
  refine Measure.ext_of_Iic _ _ fun a => ?_
  have hΦ : Measurable ((Iic a).indicator (1 : ℝ → ℝ)) :=
    measurable_one.indicator measurableSet_Iic
  -- The mass of `(-∞, a]` under the law of `K` is the integral of the indicator along `K`.
  have hmass : ∀ K : Ω → ℝ, Measurable K →
      (μ.map K).real (Iic a) = ∫ x, (Iic a).indicator (1 : ℝ → ℝ) (K x) ∂μ := by
    intro K hK
    rw [← integral_indicator_one measurableSet_Iic,
      integral_map hK.aemeasurable hΦ.aestronglyMeasurable]
  have hreal : (μ.map F).real (Iic a) = (μ.map G).real (Iic a) :=
    (hmass F hF).trans ((h _ hΦ).trans (hmass G hG).symm)
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 hreal

end Riesz1

end
