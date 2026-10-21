/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Frozen.Variance
public import Mathlib.Probability.Moments.Variance

/-!
# Removing a size weight from a variance

An observable that vanishes above a density threshold has its weighted variance
bounded by the unweighted variance and the mass of the density tail. This is the
measure theoretic step of Lemma 5.8.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Riesz1

/-- Variance is the least squared error over constant predictors. The variance
on the left is the extended valued variance. -/
theorem variance_le_lintegral_sq_sub {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {F : Ω → ℝ}
    (hF : MemLp F 2 μ) (c : ℝ) :
    variance μ F (hF.integrable one_le_two) ≤
      ∫⁻ x, ENNReal.ofReal ((F x - c) ^ 2) ∂μ := by
  have hFc : MemLp (fun x => F x - c) 2 μ := hF.sub (memLp_const c)
  have hs : Integrable (fun x => (F x - c) ^ 2) μ := hFc.integrable_sq
  rw [variance, ← ProbabilityTheory.evariance_eq_lintegral_ofReal,
    ← ProbabilityTheory.ofReal_variance hF,
    ← ofReal_integral_eq_lintegral_ofReal hs (ae_of_all _ fun x => sq_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  calc ProbabilityTheory.variance F μ = ProbabilityTheory.variance (fun x => F x - c) μ :=
      (ProbabilityTheory.variance_sub_const hF.aestronglyMeasurable c).symm
    _ ≤ ∫ x, (F x - c) ^ 2 ∂μ :=
      ProbabilityTheory.variance_le_expectation_sq hFc.aestronglyMeasurable

/-- If `F` vanishes when `w > T`, the contribution of that density tail to the
squared error about the base mean is exactly the squared base mean times its
weighted probability. No independence assumption is used. -/
theorem sizeBiased_variance_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {w F : Ω → ℝ}
    (hw : Measurable w) (hF : MemLp F 2 μ)
    [IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (w x)))]
    (hFw : MemLp F 2 (μ.withDensity (fun x => ENNReal.ofReal (w x))))
    {T : ℝ} (_hT : 0 ≤ T) (hzero : ∀ᵐ x ∂μ, T < w x → F x = 0) :
    variance (μ.withDensity (fun x => ENNReal.ofReal (w x))) F
        (hFw.integrable one_le_two) ≤
      ENNReal.ofReal T * variance μ F (hF.integrable one_le_two) +
        ENNReal.ofReal ((∫ x, F x ∂μ) ^ 2) *
          μ.withDensity (fun x => ENNReal.ofReal (w x)) {x | T < w x} := by
  let c := ∫ x, F x ∂μ
  let E := {x | T < w x}
  have hE : MeasurableSet E := measurableSet_lt measurable_const hw
  apply (variance_le_lintegral_sq_sub _ hFw c).trans
  rw [lintegral_withDensity_eq_lintegral_mul₀ hw.ennreal_ofReal.aemeasurable
    ((hF.aemeasurable.sub_const c).pow_const 2).ennreal_ofReal]
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal T * ENNReal.ofReal ((F x - c) ^ 2) +
        ENNReal.ofReal (c ^ 2) * E.indicator (fun x => ENNReal.ofReal (w x)) x ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hzero] with x hx
      by_cases he : x ∈ E
      · have hz := hx he
        simp only [Pi.mul_apply, hz, zero_sub, neg_sq, Set.indicator_of_mem he]
        rw [mul_comm (ENNReal.ofReal (w x))]
        exact le_add_left le_rfl
      · rw [Set.indicator_of_notMem he, mul_zero, add_zero]
        change ENNReal.ofReal (w x) * _ ≤ _
        gcongr
        exact not_lt.mp he
    _ = ENNReal.ofReal T * (∫⁻ x, ENNReal.ofReal ((F x - c) ^ 2) ∂μ) +
        ENNReal.ofReal (c ^ 2) * ∫⁻ x, E.indicator (fun x => ENNReal.ofReal (w x)) x ∂μ := by
      rw [lintegral_add_left'
        ((((hF.aemeasurable.sub_const c).pow_const 2).ennreal_ofReal).const_mul _),
        lintegral_const_mul'' _ (((hF.aemeasurable.sub_const c).pow_const 2).ennreal_ofReal),
        lintegral_const_mul'' _ ((hw.ennreal_ofReal.indicator hE).aemeasurable)]
    _ = _ := by
      rw [lintegral_indicator hE, ← withDensity_apply _ hE]
      rfl

end Riesz1

end
