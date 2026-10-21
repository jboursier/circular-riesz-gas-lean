/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopSizeBiasOffsets

/-!
# The displacement coordinate of a uniformly rotated particle

Change-of-variables ingredients for the joint-law clause of
the size-bias part of Lemma 5.8.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Riesz1.Internal

/-- The forward microscopic circular displacement from a given particle to zero. -/
def loopRotationDisplacement (N : ℕ+) (u : UnitAddCircle) : ℝ :=
  (N : ℝ) * (AddCircle.equivIco (1 : ℝ) 0 (0 - u) : ℝ)

theorem measurable_loopRotationDisplacement (N : ℕ+) : Measurable (loopRotationDisplacement N) :=
  (measurable_subtype_coe.comp
    ((AddCircle.measurableEquivIco (1 : ℝ) 0).measurable.comp (by fun_prop))).const_mul _

/-- Uniform rotation gives Lebesgue measure divided by `N` on the displacement interval. -/
theorem map_loopRotationDisplacement (N : ℕ+) :
    (volume : Measure UnitAddCircle).map (loopRotationDisplacement N) =
      ENNReal.ofReal ((N : ℝ)⁻¹) • volume.restrict (Ico (0 : ℝ) N) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  let r : UnitAddCircle → ℝ := fun u => (AddCircle.equivIco (1 : ℝ) 0 u : ℝ)
  have hr : Measurable r :=
    measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable
  have hrot : (volume : Measure UnitAddCircle).map (fun u => r (0 - u)) =
      volume.restrict (Ico (0 : ℝ) 1) := by
    rw [show (fun u => r (0 - u)) = r ∘ (fun u => 0 - u) from rfl,
      ← Measure.map_map hr (by fun_prop),
      (volume : Measure UnitAddCircle).measurePreserving_sub_left 0 |>.map_eq,
      map_circle_representative_uniform]
  have he : loopRotationDisplacement N = (fun t : ℝ => (N : ℝ) * t) ∘ (fun u => r (0 - u)) := rfl
  have hmr : Measurable (fun u => r (0 - u)) := hr.comp (by fun_prop)
  rw [he, ← Measure.map_map (by fun_prop) hmr, hrot]
  ext B hB
  rw [Measure.map_apply (by fun_prop) hB, Measure.restrict_apply (by measurability),
    Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hB]
  have hset : (fun t : ℝ => (N : ℝ) * t) ⁻¹' B ∩ Ico (0 : ℝ) 1 =
      (fun t : ℝ => (N : ℝ) * t) ⁻¹' (B ∩ Ico (0 : ℝ) N) := by
    ext t
    simp only [mem_inter_iff, mem_preimage, mem_Ico]
    have h0 : 0 ≤ (N : ℝ) * t ↔ 0 ≤ t := mul_nonneg_iff_of_pos_left hN
    have h1 : (N : ℝ) * t < N ↔ t < 1 := by
      simpa only [mul_one] using (mul_lt_mul_iff_of_pos_left hN : (N : ℝ) * t < N * 1 ↔ t < 1)
    simp only [h0, h1]
  rw [hset, Real.volume_preimage_mul_left hN.ne', abs_of_pos (inv_pos.mpr hN)]

/-- The rooted gap vector together with the displacement from a specified particle. -/
def loopParticlePair (N : ℕ+) (i : Fin (N : ℕ)) (X : Configuration N) :
    (Fin (N : ℕ) → ℝ) × ℝ :=
  (shiftFin N (i : ℕ) (gapVector X), loopRotationDisplacement N (cyclicLift X (i : ℕ)))

theorem measurable_loopParticlePair (N : ℕ+) (i : Fin (N : ℕ)) : Measurable (loopParticlePair N i) :=
  ((measurable_shiftFin _).comp (measurable_gapVector N)).prodMk
    ((measurable_loopRotationDisplacement N).comp
      (measurable_coe_circle.comp (measurable_cyclicLift _)))

/-- Before selection, a particle's displacement and its whole rooted gap vector are independent. -/
theorem map_loopParticlePair (P : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (i : Fin (N : ℕ)) :
    (gibbsMeasure P N).map (loopParticlePair N i) =
      ((gibbsMeasure P N).map gapVector).prod
        (ENNReal.ofReal ((N : ℝ)⁻¹) • volume.restrict (Ico (0 : ℝ) N)) := by
  have := (modelWellDefined P N).2.2
  have hJ : Measurable (fun X : Configuration N => ((cyclicLift X (i : ℕ) : UnitAddCircle), gapVector X)) :=
    (measurable_coe_circle.comp (measurable_cyclicLift _)).prodMk (measurable_gapVector N)
  have hm : Measurable (Prod.map (loopRotationDisplacement N) (shiftFin N (i : ℕ))) :=
    (measurable_loopRotationDisplacement N).prodMap (measurable_shiftFin _)
  have h := congrArg (fun μ => (μ.map (Prod.map (loopRotationDisplacement N)
      (shiftFin N (i : ℕ)))).map Prod.swap)
    (map_cyclicLift_gapVector_gibbsMeasure P N (i : ℕ))
  rw [Measure.map_map hm hJ, ← Measure.map_prod_map _ _
    (measurable_loopRotationDisplacement N) (measurable_shiftFin _),
    Measure.prod_swap, map_loopRotationDisplacement,
    Measure.map_map (measurable_shiftFin _) (measurable_gapVector N)] at h
  simp only [Function.comp_def] at h
  rw [map_shiftFin_gibbsMeasure P hN i.val] at h
  have hm2 : Measurable (fun X : Configuration N =>
      Prod.map (loopRotationDisplacement N) (shiftFin N (i : ℕ))
        ((cyclicLift X (i : ℕ) : UnitAddCircle), gapVector X)) := hm.comp hJ
  rw [Measure.map_map measurable_swap hm2] at h
  exact h

end Riesz1.Internal

end
