/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopSizeBiasDefs

/-!
# The anchored size weight has mean one

The size-bias part of Lemma 5.8, normalization. Here `N = n + 2`, and `P*` is
`anchoredLaw P (n + 1)`. The weight is the following microscopic nearest gap.
-/

public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal

namespace Riesz1

theorem measurable_loopSizeWeight (n : ℕ) : Measurable (loopSizeWeight n) := by
  unfold loopSizeWeight
  fun_prop

/-- The size weight pulled back along anchoring is the microscopic gap at label zero. -/
theorem loopSizeWeight_anchorCoords (n : ℕ) (X : Configuration (n + 1).succPNat) :
    loopSizeWeight n (anchorCoords (n + 1) X.val).2 = gap X 0 := by
  have h1 : cyclicLift X 1 = X.val ⟨1, by simp⟩ :=
    cyclicLift_natCast X ⟨1, by simp⟩
  rw [gap, zero_add, h1, cyclicLift_zero]
  rfl

theorem loopSizeWeight_nonneg_ae (P : Parameters) (n : ℕ) :
    0 ≤ᵐ[anchoredLaw P (n + 1)] loopSizeWeight n := by
  rw [← map_snd_gibbsMeasure P (n + 1)]
  apply (ae_map_iff (measurable_snd.comp (measurable_anchorCoords_config (n + 1))).aemeasurable
    (measurableSet_le (show Measurable (fun _ : Fin (n + 1) → ℝ => (0 : ℝ)) from measurable_const)
      (measurable_loopSizeWeight n))).mpr
  exact ae_of_all _ fun X => by
    change 0 ≤ loopSizeWeight n (anchorCoords (n + 1) X.val).2
    rw [loopSizeWeight_anchorCoords]
    exact (gap_pos X 0).le

theorem integrable_loopSizeWeight (P : Parameters) (n : ℕ) :
    Integrable (loopSizeWeight n) (anchoredLaw P (n + 1)) := by
  rw [← map_snd_gibbsMeasure P (n + 1)]
  apply (integrable_map_measure (measurable_loopSizeWeight n).aestronglyMeasurable
    (measurable_snd.comp (measurable_anchorCoords_config (n + 1))).aemeasurable).mpr
  simpa only [Function.comp_def, loopSizeWeight_anchorCoords] using
    integrable_gap P (n + 1).succPNat 0

/-- The size-bias part of Lemma 5.8: `E_{P*} w = 1`. -/
theorem integral_loopSizeWeight (P : Parameters) (n : ℕ) :
    ∫ y, loopSizeWeight n y ∂anchoredLaw P (n + 1) = 1 := by
  have hm : Measurable (fun X : Configuration (n + 1).succPNat => (anchorCoords (n + 1) X.val).2) :=
    measurable_snd.comp (measurable_anchorCoords_config (n + 1))
  rw [← map_snd_gibbsMeasure P (n + 1),
    integral_map hm.aemeasurable
      (measurable_loopSizeWeight n).aestronglyMeasurable]
  simp_rw [loopSizeWeight_anchorCoords]
  exact integral_gap_gibbsMeasure P (n + 1).succPNat (by simp) 0

/-- The measure `w P*` is a probability measure. -/
instance isProbabilityMeasure_loopSizeBiasedLaw (P : Parameters) (n : ℕ) :
    IsProbabilityMeasure (loopSizeBiasedLaw P n) := by
  constructor
  rw [loopSizeBiasedLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_loopSizeWeight P n)
      (loopSizeWeight_nonneg_ae P n), integral_loopSizeWeight, ENNReal.ofReal_one]

end Riesz1

end
