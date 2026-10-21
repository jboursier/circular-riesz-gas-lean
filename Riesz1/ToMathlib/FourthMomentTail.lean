/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.LogConcave.EventSecondMoment
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# A real second moment from a fourth moment and one tail bound

The bounded part contributes the square of the cutoff. Cauchy--Schwarz
controls the remaining event. Integrability is included in the conclusion.
-/

public section

open Set MeasureTheory

namespace Riesz1

/-- A fourth-moment and a tail bound control the second moment. -/
theorem second_moment_le_cutoff_add_sqrt {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : Ω → ℝ} (hZ : Measurable Z)
    (hi4 : Integrable (fun x => Z x ^ 4) μ) {D t T : ℝ}
    (_ht : 0 ≤ t) (h4 : (∫ x, Z x ^ 4 ∂μ) ≤ D)
    (hT : μ.real {x | t ≤ |Z x|} ≤ T) :
    Integrable (fun x => Z x ^ 2) μ ∧
      (∫ x, Z x ^ 2 ∂μ) ≤ t ^ 2 + Real.sqrt D * Real.sqrt T := by
  have hi22 : Integrable (fun x => (Z x ^ 2) ^ 2) μ := by
    simpa only [← pow_mul] using hi4
  have hm : MemLp (fun x => Z x ^ 2) 2 μ :=
    (memLp_two_iff_integrable_sq (hZ.pow_const 2).aestronglyMeasurable).mpr hi22
  have hi := hm.integrable (by norm_num)
  refine ⟨hi, ?_⟩
  let E : Set Ω := {x | t ≤ |Z x|}
  have hE : MeasurableSet E := measurableSet_le measurable_const (continuous_abs.measurable.comp hZ)
  have hb := integral_on_event_le_second_moment (hZ.pow_const 2).aestronglyMeasurable
    (fun x => sq_nonneg (Z x)) hi22 hE
  simp only [← Real.sqrt_eq_rpow, ← pow_mul] at hb
  have hgood : (∫ x in Eᶜ, Z x ^ 2 ∂μ) ≤ t ^ 2 := by
    calc (∫ x in Eᶜ, Z x ^ 2 ∂μ) ≤ ∫ _x in Eᶜ, t ^ 2 ∂μ := by
          apply setIntegral_mono_on hi.integrableOn (integrable_const _) hE.compl
          intro x hx
          have hx' : |Z x| ≤ t := (not_le.mp (show ¬t ≤ |Z x| from hx)).le
          simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (Z x)) hx' 2
      _ = μ.real Eᶜ * t ^ 2 := by rw [setIntegral_const, smul_eq_mul]
      _ ≤ t ^ 2 := by
          exact (mul_le_mul_of_nonneg_right measureReal_le_one (sq_nonneg t)).trans_eq (one_mul _)
  rw [← integral_add_compl hE hi]
  have hbad : (∫ x in E, Z x ^ 2 ∂μ) ≤ Real.sqrt D * Real.sqrt T :=
    hb.trans (mul_le_mul (Real.sqrt_le_sqrt h4) (Real.sqrt_le_sqrt hT)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  linarith

end Riesz1
