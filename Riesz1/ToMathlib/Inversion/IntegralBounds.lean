/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.WeightedSobolev.L2Facts

/-!
# Ordinary integral bounds from nonnegative second moments

Integrability is derived before using real integrals. These lemmas are
used for the averaging argument that removes nearest-particle bias.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Riesz1

lemma inversion_memLp_two_of_secondMoment {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → ℝ} (hf : Measurable f) {D : ℝ} (hD : 0 ≤ D)
    (h : ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ ≤ ENNReal.ofReal D) :
    MemLp f 2 μ ∧ (∫ x, f x ^ 2 ∂μ) ≤ D := by
  have hi : Integrable (fun x => f x ^ 2) μ := by
    refine ⟨(hf.pow_const 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => sq_nonneg _)]
    exact h.trans_lt ENNReal.ofReal_lt_top
  refine ⟨(memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr hi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun x => sq_nonneg _)] at h
  exact (ENNReal.ofReal_le_ofReal_iff hD).mp h

/-- Cauchy--Schwarz with explicit bounds on both nonnegative second moments. -/
lemma inversion_integral_abs_mul_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f g : Ω → ℝ} (hf : Measurable f) (hg : Measurable g)
    {D E : ℝ} (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hf2 : ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ ≤ ENNReal.ofReal D)
    (hg2 : ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂μ ≤ ENNReal.ofReal E) :
    Integrable (fun x => |f x| * |g x|) μ ∧
      (∫ x, |f x| * |g x| ∂μ) ≤ Real.sqrt D * Real.sqrt E := by
  obtain ⟨hfl, hfi⟩ := inversion_memLp_two_of_secondMoment hf hD hf2
  obtain ⟨hgl, hgi⟩ := inversion_memLp_two_of_secondMoment hg hE hg2
  have hfa : MemLp (fun x => |f x|) 2 μ := by
    simpa only [Real.norm_eq_abs] using hfl.norm
  have hga : MemLp (fun x => |g x|) 2 μ := by
    simpa only [Real.norm_eq_abs] using hgl.norm
  refine ⟨hfa.integrable_mul hga, ?_⟩
  have h := WeightedSobolev.abs_integral_mul_le_sqrt hfa hga
  simp only [sq_abs] at h
  rw [abs_of_nonneg (integral_nonneg fun x => mul_nonneg (abs_nonneg _) (abs_nonneg _))] at h
  exact h.trans (mul_le_mul (Real.sqrt_le_sqrt hfi) (Real.sqrt_le_sqrt hgi)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-- A second moment controls the first absolute moment on a probability space. -/
lemma inversion_integral_abs_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Measurable f)
    {D : ℝ} (hD : 0 ≤ D)
    (hf2 : ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ ≤ ENNReal.ofReal D) :
    Integrable f μ ∧ (∫ x, |f x| ∂μ) ≤ Real.sqrt D := by
  have h1 : ∫⁻ x : Ω, ENNReal.ofReal ((1 : ℝ) ^ 2) ∂μ ≤ ENNReal.ofReal 1 := by simp
  obtain ⟨hi, hb⟩ := inversion_integral_abs_mul_le hf measurable_const hD zero_le_one hf2 h1
  simp only [abs_one, mul_one, Real.sqrt_one] at hi hb
  exact ⟨(integrable_norm_iff hf.aestronglyMeasurable).mp (by simpa only [Real.norm_eq_abs] using hi), hb⟩

end Riesz1

end
end
