/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Measure.Restrict

/-!
# Norms on a measurable subtype

Restricting the configuration carrier to a measurable event restricts the measure.
Pullback to that subtype cannot increase an extended `L^p` norm or event probability.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Riesz1

/-- Pullback to a measurable subtype has the same norm as restriction of the measure. -/
theorem eLpNorm_subtype_eq_restrict {Ω : Type*} [MeasurableSpace Ω]
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (μ : Measure Ω) {S : Set Ω} (hS : MeasurableSet S)
    {f : Ω → E} (hf : Measurable f) (p : ℝ≥0∞) :
    eLpNorm (fun x : S => f x.val) p (μ.comap (Subtype.val : S → Ω)) =
      eLpNorm f p (μ.restrict S) := by
  rw [← map_comap_subtype_coe hS μ]
  exact (eLpNorm_map_measure hf.aestronglyMeasurable measurable_subtype_coe.aemeasurable).symm

/-- Restricting to a measurable subtype cannot increase the norm. -/
theorem eLpNorm_subtype_le {Ω : Type*} [MeasurableSpace Ω]
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (μ : Measure Ω) {S : Set Ω} (hS : MeasurableSet S)
    {f : Ω → E} (hf : Measurable f) (p : ℝ≥0∞) :
    eLpNorm (fun x : S => f x.val) p (μ.comap (Subtype.val : S → Ω)) ≤ eLpNorm f p μ := by
  rw [eLpNorm_subtype_eq_restrict μ hS hf p]
  exact eLpNorm_restrict_le f p μ S

/-- An event on the restricted subtype is bounded by the same event on the whole carrier. -/
theorem measure_subtype_preimage_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {S : Set Ω} (hS : MeasurableSet S) (T : Set Ω) :
    μ.comap (Subtype.val : S → Ω) (Subtype.val ⁻¹' T) ≤ μ T := by
  rw [comap_subtype_coe_apply hS]
  apply measure_mono
  rintro x ⟨y, hy, rfl⟩
  exact hy

end Riesz1

end
