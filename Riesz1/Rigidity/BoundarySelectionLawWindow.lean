/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.BoundarySelectionLawGeometry
public import Mathlib.MeasureTheory.Group.AddCircle

/-!
# Uniform rotation window probabilities

The Haar measure of the fractional rotation window occurring in boundary selection.
-/

public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

/-- The canonical real representative of uniform circle arclength is uniform on `[0,1)`. -/
theorem map_circle_representative_uniform :
    (volume : Measure UnitAddCircle).map (fun u => (AddCircle.equivIco (1 : ℝ) 0 u : ℝ)) =
      volume.restrict (Ico (0 : ℝ) 1) := by
  have hm : Measurable (fun u : UnitAddCircle => (AddCircle.equivIco (1 : ℝ) 0 u : ℝ)) :=
    measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable
  have hcoe : (volume.restrict (Ico (0 : ℝ) 1)).map (fun t : ℝ => (t : UnitAddCircle)) = volume := by
    simpa only [add_zero] using map_circle_translate_uniform 0
  rw [← hcoe, Measure.map_map hm measurable_coe_circle]
  have he : (fun t : ℝ => (AddCircle.equivIco (1 : ℝ) 0 (t : UnitAddCircle) : ℝ)) =ᵐ[
      volume.restrict (Ico (0 : ℝ) 1)] id := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with t ht
    exact AddCircle.equivIco_coe_of_mem (by simpa only [zero_add] using ht)
  simp only [Function.comp_def]
  rw [Measure.map_congr he, Measure.map_id]

/-- A fractional rotation window of length `d ∈ [0,1]` has arclength `d`. -/
theorem circle_rotation_window_volume (b : UnitAddCircle) {d : ℝ}
    (_hd : 0 ≤ d) (hd1 : d ≤ 1) :
    (volume : Measure UnitAddCircle) {u | (AddCircle.equivIco (1 : ℝ) 0 (b - u) : ℝ) < d} =
      ENNReal.ofReal d := by
  have hm : Measurable (fun u : UnitAddCircle => (AddCircle.equivIco (1 : ℝ) 0 u : ℝ)) :=
    measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable
  have he : (volume : Measure UnitAddCircle).map
      (fun u => (AddCircle.equivIco (1 : ℝ) 0 (b - u) : ℝ)) = volume.restrict (Ico (0 : ℝ) 1) := by
    rw [show (fun u : UnitAddCircle => (AddCircle.equivIco (1 : ℝ) 0 (b - u) : ℝ)) =
      (fun u => (AddCircle.equivIco (1 : ℝ) 0 u : ℝ)) ∘ (fun u => b - u) from rfl,
      ← Measure.map_map hm (by fun_prop), (volume : Measure UnitAddCircle).measurePreserving_sub_left b |>.map_eq,
      map_circle_representative_uniform]
  have hh := congrArg (fun μ : Measure ℝ => μ (Iio d)) he
  have hmeas : Measurable (fun u : UnitAddCircle => (AddCircle.equivIco (1 : ℝ) 0 (b - u) : ℝ)) := hm.comp (by fun_prop)
  rw [Measure.map_apply hmeas measurableSet_Iio,
    Measure.restrict_apply measurableSet_Iio] at hh
  have hset : Iio d ∩ Ico (0 : ℝ) 1 = Ico 0 d := by
    ext t
    simp only [mem_inter_iff, mem_Iio, mem_Ico]
    constructor
    · rintro ⟨ht, ht0, _⟩
      exact ⟨ht0, ht⟩
    · rintro ⟨ht0, ht⟩
      exact ⟨ht, ht0, ht.trans_le hd1⟩
  rw [hset, Real.volume_Ico, sub_zero] at hh
  exact hh

end Riesz1

end
