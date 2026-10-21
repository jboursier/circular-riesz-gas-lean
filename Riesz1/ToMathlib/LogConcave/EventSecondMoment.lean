/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Function.L2Space

/-!
# A second-moment bound on an event

Cauchy--Schwarz with an event indicator, used for boundary size bias.
-/

public section

open MeasureTheory Set

namespace Riesz1

/-- Cauchy--Schwarz bounds an expectation restricted to an event. -/
theorem integral_on_event_le_second_moment {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {Y : Ω → ℝ} (hY : AEStronglyMeasurable Y μ)
    (hpos : ∀ x, 0 ≤ Y x) (hi : Integrable (fun x => Y x ^ 2) μ)
    {E : Set Ω} (hE : MeasurableSet E) :
    (∫ x in E, Y x ∂μ) ≤ (∫ x, Y x ^ 2 ∂μ) ^ (1 / (2 : ℝ)) * μ.real E ^ (1 / (2 : ℝ)) := by
  have hf : MemLp Y 2 μ := (memLp_two_iff_integrable_sq hY).mpr hi
  have hg : MemLp (E.indicator (fun _ => (1 : ℝ))) 2 μ := (memLp_const 1).indicator hE.nullMeasurableSet
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (ae_of_all _ hpos) (ae_of_all μ fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x)
    (by simpa only [ENNReal.ofReal_ofNat] using hf)
    (by simpa only [ENNReal.ofReal_ofNat] using hg)
  have he : (fun x => Y x * E.indicator (fun _ => (1 : ℝ)) x) = E.indicator Y := by
    funext x
    by_cases hx : x ∈ E <;> simp [hx]
  have hpow : (fun x => (E.indicator (fun _ => (1 : ℝ)) x) ^ (2 : ℝ)) =
      E.indicator (fun _ => (1 : ℝ)) := by
    funext x
    by_cases hx : x ∈ E <;> simp [hx]
  rw [he, integral_indicator hE, hpow, integral_indicator hE, setIntegral_const,
    smul_eq_mul, mul_one] at hh
  simpa only [Real.rpow_two] using hh

end Riesz1
