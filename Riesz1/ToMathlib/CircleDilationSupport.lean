/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.PeriodicScaledMarkCutoff

/-!
# Supports under circle dilation

Metric balls on an additive circle are projected real intervals, including
when the interval covers the circle. Circle dilation scales every distance
by the ratio of the periods. These facts also cover circles of length one.
-/

public section

open Set

namespace Riesz1

theorem coe_cutRep (L x : ℝ) : (cutRep L x : AddCircle L) = (x : AddCircle L) := by
  unfold cutRep
  rw [AddCircle.coe_sub, mul_comm L, ← zsmul_eq_mul, AddCircle.coe_zsmul,
    AddCircle.coe_period, smul_zero, sub_zero]

/-- A closed circle ball is the image of the real interval with the same
center and radius. No restriction relative to the period is needed. -/
theorem circle_closedBall_eq_image_interval (L a R : ℝ) :
    Metric.closedBall (a : AddCircle L) R =
      (fun t : ℝ => (t : AddCircle L)) '' Icc (a-R) (a+R) := by
  ext z
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  constructor
  · intro hx
    have hd : |cutRep L (x-a)| ≤ R := by
      rw [abs_cutRep_eq_dist]
      exact hx
    refine ⟨a + cutRep L (x-a), ?_, ?_⟩
    · obtain ⟨h0, h1⟩ := abs_le.mp hd
      constructor <;> linarith
    · change ((a + cutRep L (x-a) : ℝ) : AddCircle L) = (x : AddCircle L)
      rw [AddCircle.coe_add, coe_cutRep, AddCircle.coe_sub]
      abel
  · rintro ⟨t, ht, he⟩
    rw [← he, Metric.mem_closedBall, dist_eq_norm, ← AddCircle.coe_sub]
    calc
      _ ≤ |t-a| := QuotientAddGroup.norm_mk_le_norm
      _ ≤ R := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩

theorem circleDilation_dist {T L : ℝ} (hT : 0 < T) (hL : 0 < L)
    (u v : AddCircle T) :
    dist (AddCircle.equivAddCircle T L hT.ne' hL.ne' u)
      (AddCircle.equivAddCircle T L hT.ne' hL.ne' v) = (L/T) * dist u v := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective u
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective v
  simp only [AddCircle.equivAddCircle_apply_mk, dist_eq_norm, ← AddCircle.coe_sub]
  rw [AddCircle.norm_eq' L hL, AddCircle.norm_eq' T hT]
  have he : L⁻¹ * (x * (T⁻¹ * L) - y * (T⁻¹ * L)) = T⁻¹ * (x-y) := by
    field_simp
  rw [he]
  field_simp

end Riesz1
