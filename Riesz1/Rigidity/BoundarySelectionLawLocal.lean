/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.BoundarySelectionLawWindow

/-!
# One-label boundary selection law

The size-bias identity for one cyclic label and an arbitrary Borel gap event.
-/

public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

/-- The contribution of a fixed cyclic label to the boundary-selected event. -/
theorem boundary_selection_one_label (P : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (a : UnitAddCircle) (ℓ : ℝ) (i : Fin (N : ℕ))
    (A : Set (Fin (N : ℕ) → ℝ)) (hA : MeasurableSet A) :
    (gibbsMeasure P N) {X | (∃ q : ℤ,
      precedingLabel a ℓ X = (i : ℕ) + ((N : ℕ) : ℤ) * q) ∧ gapVector X ∈ A} =
      ∫⁻ X in gapVector ⁻¹' A, ENNReal.ofReal (gap X (i : ℕ) / (N : ℝ)) ∂gibbsMeasure P N := by
  let := (modelWellDefined P N).2.2
  let ν := (gibbsMeasure P N).map gapVector
  let b : UnitAddCircle := (leftLift a ℓ : ℝ)
  let B : Set (UnitAddCircle × (Fin (N : ℕ) → ℝ)) :=
    {p | (AddCircle.equivIco (1 : ℝ) 0 (b - p.1) : ℝ) < p.2 i / (N : ℝ) ∧ p.2 ∈ A}
  have hmrep : Measurable (fun u : UnitAddCircle => (AddCircle.equivIco (1 : ℝ) 0 u : ℝ)) :=
    measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable
  have hB : MeasurableSet B := (measurableSet_lt (hmrep.comp (by fun_prop))
    (((measurable_pi_apply i).comp measurable_snd).div_const _)).inter (measurable_snd hA)
  have hJ : Measurable (fun X : Configuration N => ((cyclicLift X (i : ℕ) : UnitAddCircle), gapVector X)) :=
    (measurable_coe_circle.comp (measurable_cyclicLift _)).prodMk (measurable_gapVector N)
  have hpre : (fun X : Configuration N => ((cyclicLift X (i : ℕ) : UnitAddCircle), gapVector X)) ⁻¹' B =
      {X | (∃ q : ℤ, precedingLabel a ℓ X = (i : ℕ) + ((N : ℕ) : ℤ) * q) ∧ gapVector X ∈ A} := by
    ext X
    change ((AddCircle.equivIco (1 : ℝ) 0 ((leftLift a ℓ : UnitAddCircle) - (cyclicLift X (i : ℕ) : UnitAddCircle)) : ℝ) < gap X (i : ℕ) / (N : ℝ) ∧ gapVector X ∈ A) ↔ ((∃ q : ℤ, precedingLabel a ℓ X = (i : ℕ) + ((N : ℕ) : ℤ) * q) ∧ gapVector X ∈ A)
    rw [precedingLabel_cyclic_iff_fract hN a ℓ X (i : ℕ)]
    apply and_congr_left
    intro _
    rw [← AddCircle.coe_sub]
    change (AddCircle.equivIco (1 : ℝ) 0 (QuotientAddGroup.mk (leftLift a ℓ - cyclicLift X (i : ℕ))) : ℝ) < _ ↔ _
    simp only [AddCircle.coe_equivIco_mk_apply, div_one, mul_one]
  rw [← hpre, ← Measure.map_apply hJ hB, map_cyclicLift_gapVector_gibbsMeasure,
    Measure.prod_apply_symm hB]
  have hNr : (0 : ℝ) < (N : ℕ) := by exact_mod_cast N.pos
  have hsupp : ∀ᵐ y ∂ν, 0 ≤ y i / (N : ℝ) ∧ y i / (N : ℝ) ≤ 1 := by
    apply (ae_map_iff (measurable_gapVector N).aemeasurable (by measurability)).mpr
    exact ae_of_all _ fun X => ⟨div_nonneg (gap_pos X _).le hNr.le,
      (div_le_one hNr).mpr (gap_le_N X _)⟩
  have he : ∀ᵐ y ∂ν,
      (volume : Measure UnitAddCircle) ((fun u => (u, y)) ⁻¹' B) =
        A.indicator (fun y => ENNReal.ofReal (y i / (N : ℝ))) y := by
    filter_upwards [hsupp] with y hy
    by_cases hyA : y ∈ A
    · simp only [Set.indicator_of_mem hyA]
      change volume {u : UnitAddCircle | (AddCircle.equivIco (1 : ℝ) 0 (b - u) : ℝ) <
        y i / (N : ℝ) ∧ y ∈ A} = _
      simp only [hyA, and_true]
      exact circle_rotation_window_volume b hy.1 hy.2
    · simp only [Set.indicator_of_notMem hyA]
      change volume {u : UnitAddCircle | _ ∧ y ∈ A} = 0
      simp only [hyA, and_false, Set.ofPred_false, measure_empty]
  rw [lintegral_congr_ae he, lintegral_map
    ((((measurable_pi_apply i).div_const _).ennreal_ofReal).indicator hA)
    (measurable_gapVector N)]
  rw [← lintegral_indicator (measurable_gapVector N hA)]
  congr 1

end Riesz1

end
