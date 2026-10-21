/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.GapsDiscStripsArc

/-!
# The difference of two concentric arcs

For `0 < lo ≤ hi < 1/2`, the indicator of the annulus `{lo ≤ |x| < hi}` on the circle is, up to a
null set, the sum of the indicators of two open arcs of half-width `d = (hi - lo)/2` centred at
`±c` with `c = (lo + hi)/2`. This is the geometric input of the second assertion of the strip
lemma in the proof of Corollary 1.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace Riesz1

/-- Real representatives: `y - round y` lies in `[-1/2, 1/2)`. -/
lemma sub_round_mem_Ico (y : ℝ) : -(1 / 2) ≤ y - round y ∧ y - round y < 1 / 2 := by
  have h1 := Int.floor_le (y + 1 / 2)
  have h2 := Int.lt_floor_add_one (y + 1 / 2)
  rw [← round_eq] at h1 h2
  constructor <;> linarith [h1, h2]

/-- The distance between the classes of two reals on the unit circle, through the rounding
representative. -/
lemma dist_coe_coe_eq (u e : ℝ) :
    dist (u : UnitAddCircle) (e : UnitAddCircle) = |(u - e) - round (u - e)| := by
  rw [dist_eq_norm, ← AddCircle.coe_sub, UnitAddCircle.norm_eq]

/-- For a representative `u ∈ [-1/2, 1/2)` and a centre `e` with `|e| + d < 1/2`, the circle
distance from `u` to `e` is less than `d` exactly when `|u - e| < d`. -/
lemma dist_coe_lt_iff_abs_lt (u e d : ℝ) (hu1 : -(1 / 2) ≤ u) (hu2 : u < 1 / 2)
    (he : |e| + d < 1 / 2) (hd : 0 ≤ d) :
    dist (u : UnitAddCircle) (e : UnitAddCircle) < d ↔ |u - e| < d := by
  have he1 : |e| < 1 / 2 := by linarith
  have hed : e < 1 / 2 - d := by linarith [le_abs_self e]
  have hed' : d - 1 / 2 < e := by linarith [neg_abs_le e]
  have hd2 : d < 1 / 2 := by linarith [abs_nonneg e]
  rw [dist_coe_coe_eq]
  rcases lt_or_ge (u - e) (-(1 / 2)) with hlow | hlow
  · -- the rounding integer is `-1`, and the distance is `u - e + 1`
    have hr : round (u - e) = -1 := by
      rw [round_eq, Int.floor_eq_iff]
      constructor <;> push_cast <;> linarith
    have hval : |(u - e) - ((-1 : ℤ) : ℝ)| = u - e + 1 := by
      push_cast
      rw [abs_of_pos (by linarith)]
      ring
    rw [hr, hval, abs_lt]
    constructor
    · intro h
      exfalso
      linarith
    · intro h
      exfalso
      linarith [h.1]
  · rcases lt_or_ge (u - e) (1 / 2) with hmid | hhigh
    · -- the rounding integer is `0`
      have hr : round (u - e) = 0 := round_eq_zero_iff.mpr ⟨hlow, hmid⟩
      rw [hr]
      simp
    · -- the rounding integer is `1`, and the distance is `1 - (u - e)`
      have hr : round (u - e) = 1 := by
        rw [round_eq, Int.floor_eq_iff]
        constructor <;> push_cast <;> linarith
      have hval : |(u - e) - ((1 : ℤ) : ℝ)| = 1 - (u - e) := by
        push_cast
        rw [abs_of_nonpos (by linarith)]
        ring
      rw [hr, hval, abs_lt]
      constructor
      · intro h
        exfalso
        linarith
      · intro h
        exfalso
        linarith [h.2]

/-- The real identity behind the annulus: for `|u| ≠ lo`, the difference of the indicators of
`|x| < hi` and `|x| < lo` equals the sum of the indicators of the arcs about `±c`, `c = (lo+hi)/2`,
of half-width `d = (hi-lo)/2`. -/
lemma annulus_real_identity (lo hi u : ℝ) (hlo : 0 < lo) (hlh : lo ≤ hi)
    (hne : |u| ≠ lo) :
    (if |u| < hi then (1 : ℝ) else 0) - (if |u| < lo then (1 : ℝ) else 0) =
      (if |u - (lo + hi) / 2| < (hi - lo) / 2 then (1 : ℝ) else 0) +
        (if |u - -((lo + hi) / 2)| < (hi - lo) / 2 then (1 : ℝ) else 0) := by
  have hu1 : u ≠ lo := fun h => hne (by rw [h, abs_of_pos hlo])
  have hu2 : u ≠ -lo := fun h => hne (by rw [h, abs_neg, abs_of_pos hlo])
  rcases le_total 0 u with h0 | h0
  · rw [abs_of_nonneg h0]
    rcases lt_or_gt_of_ne hu1 with hl | hl
    · -- `0 ≤ u < lo`: both annulus indicators are `1`, the arcs miss `u`
      rw [ite_eq_left (show u < hi by linarith), ite_eq_left (show u < lo by linarith),
        ite_eq_right (show ¬ |u - (lo + hi) / 2| < (hi - lo) / 2 by
          rw [abs_lt]; intro h; linarith [h.1]),
        ite_eq_right (show ¬ |u - -((lo + hi) / 2)| < (hi - lo) / 2 by
          rw [abs_lt]; intro h; linarith [h.2])]
      norm_num
    · -- `lo < u`: the indicator of `|x| < lo` vanishes
      rw [ite_eq_right (show ¬ u < lo by linarith),
        ite_eq_right (show ¬ |u - -((lo + hi) / 2)| < (hi - lo) / 2 by
          rw [abs_lt]; intro h; linarith [h.2])]
      by_cases hu : u < hi
      · rw [ite_eq_left hu, ite_eq_left (show |u - (lo + hi) / 2| < (hi - lo) / 2 by
          rw [abs_lt]; constructor <;> linarith)]
        norm_num
      · rw [ite_eq_right hu, ite_eq_right (show ¬ |u - (lo + hi) / 2| < (hi - lo) / 2 by
          rw [abs_lt]; intro h; linarith [h.2])]
        norm_num
  · rw [abs_of_nonpos h0]
    rcases lt_or_gt_of_ne hu2 with hl | hl
    · -- `u < -lo`: the indicator of `|x| < lo` vanishes
      rw [ite_eq_right (show ¬ -u < lo by linarith),
        ite_eq_right (show ¬ |u - (lo + hi) / 2| < (hi - lo) / 2 by
          rw [abs_lt]; intro h; linarith [h.1])]
      by_cases hu : -u < hi
      · rw [ite_eq_left hu, ite_eq_left (show |u - -((lo + hi) / 2)| < (hi - lo) / 2 by
          rw [abs_lt]; constructor <;> linarith)]
        norm_num
      · rw [ite_eq_right hu, ite_eq_right (show ¬ |u - -((lo + hi) / 2)| < (hi - lo) / 2 by
          rw [abs_lt]; intro h; linarith [h.2])]
        norm_num
    · -- `-lo < u ≤ 0`: both annulus indicators are `1`, the arcs miss `u`
      rw [ite_eq_left (show -u < hi by linarith), ite_eq_left (show -u < lo by linarith),
        ite_eq_right (show ¬ |u - (lo + hi) / 2| < (hi - lo) / 2 by
          rw [abs_lt]; intro h; linarith [h.1]),
        ite_eq_right (show ¬ |u - -((lo + hi) / 2)| < (hi - lo) / 2 by
          rw [abs_lt]; intro h; linarith [h.2])]
      norm_num

/-- The class of `y - round y` on the unit circle is the class of `y`. -/
lemma coe_sub_round_eq (y : ℝ) : ((y - round y : ℝ) : UnitAddCircle) = (y : UnitAddCircle) := by
  have hn : ((round y : ℝ) : UnitAddCircle) = 0 := by
    rw [show (round y : ℝ) = (round y : ℤ) • (1 : ℝ) by rw [zsmul_eq_mul, mul_one],
      AddCircle.coe_zsmul, AddCircle.coe_period, zsmul_zero]
  rw [AddCircle.coe_sub, hn, sub_zero]

/-- The annulus identity at a point `y` whose representative `y - round y` is not `±lo`. -/
lemma arc_difference_pointwise (lo hi : ℝ) (hlo : 0 < lo) (hlh : lo ≤ hi) (hhi : hi < 1 / 2)
    (y : ℝ) (hne : |y - round y| ≠ lo) :
    arcIndicator 0 hi (y : UnitAddCircle) - arcIndicator 0 lo (y : UnitAddCircle) =
      arcIndicator (((lo + hi) / 2 : ℝ) : UnitAddCircle) ((hi - lo) / 2) (y : UnitAddCircle) +
        arcIndicator ((-((lo + hi) / 2) : ℝ) : UnitAddCircle) ((hi - lo) / 2)
          (y : UnitAddCircle) := by
  have hmem := sub_round_mem_Ico y
  have hyu : (y : UnitAddCircle) = ((y - round y : ℝ) : UnitAddCircle) :=
    (coe_sub_round_eq y).symm
  have hdist0 : dist (y : UnitAddCircle) 0 = |y - round y| := by
    rw [dist_zero_right, UnitAddCircle.norm_eq]
  have hc : 0 ≤ (lo + hi) / 2 := by linarith
  have hd : 0 ≤ (hi - lo) / 2 := by linarith
  have hcd : |(lo + hi) / 2| + (hi - lo) / 2 < 1 / 2 := by
    rw [abs_of_nonneg hc]
    linarith
  have hcd' : |-((lo + hi) / 2)| + (hi - lo) / 2 < 1 / 2 := by
    rw [abs_neg, abs_of_nonneg hc]
    linarith
  have k0 : dist (y : UnitAddCircle) 0 < hi ↔ |y - round y| < hi := by rw [hdist0]
  have k1 : dist (y : UnitAddCircle) 0 < lo ↔ |y - round y| < lo := by rw [hdist0]
  have k2 : dist (y : UnitAddCircle) (((lo + hi) / 2 : ℝ) : UnitAddCircle) < (hi - lo) / 2 ↔
      |(y - round y) - (lo + hi) / 2| < (hi - lo) / 2 := by
    rw [hyu]
    exact dist_coe_lt_iff_abs_lt _ _ _ hmem.1 hmem.2 hcd hd
  have k3 : dist (y : UnitAddCircle) ((-((lo + hi) / 2) : ℝ) : UnitAddCircle) < (hi - lo) / 2 ↔
      |(y - round y) - -((lo + hi) / 2)| < (hi - lo) / 2 := by
    rw [hyu]
    exact dist_coe_lt_iff_abs_lt _ _ _ hmem.1 hmem.2 hcd' hd
  unfold arcIndicator
  simp only [k0, k1, k2, k3]
  exact annulus_real_identity lo hi (y - round y) hlo hlh hne

/-- A point of the unit circle is a null set (the circle volume has no null-singleton instance,
so this follows the transfer from `ℝ` as in `volume_singleton_half`). -/
lemma volume_singleton_coe (a : ℝ) : volume ({(a : UnitAddCircle)} : Set UnitAddCircle) = 0 := by
  have hmp := AddCircle.measurePreserving_mk (1 : ℝ) (a - 1 / 2)
  rw [← hmp.measure_preimage (measurableSet_singleton _).nullMeasurableSet,
    Measure.restrict_apply' measurableSet_Ioc]
  refine measure_mono_null (t := {a}) ?_ (measure_singleton _)
  rintro y ⟨hy1, hy2⟩
  have ha : a ∈ Ioc (a - 1 / 2) (a - 1 / 2 + 1) := by constructor <;> linarith
  have heq : (y : UnitAddCircle) = (a : UnitAddCircle) := hy1
  rw [AddCircle.coe_eq_coe_iff_of_mem_Ioc hy2 ha] at heq
  exact heq

/-- **The annulus as a sum of two arcs.** Off the two points `±lo` of the circle, the indicator of
the annulus `lo ≤ |x| < hi` is the sum of the indicators of the open arcs of half-width
`(hi - lo)/2` centred at `±(lo + hi)/2`. Hence the two indicators agree almost everywhere. -/
theorem arc_difference_ae (lo hi : ℝ) (hlo : 0 < lo) (hlh : lo ≤ hi) (hhi : hi < 1 / 2) :
    (fun x : UnitAddCircle => arcIndicator 0 hi x - arcIndicator 0 lo x) =ᵐ[volume]
      fun x => arcIndicator (((lo + hi) / 2 : ℝ) : UnitAddCircle) ((hi - lo) / 2) x +
        arcIndicator ((-((lo + hi) / 2) : ℝ) : UnitAddCircle) ((hi - lo) / 2) x := by
  refine ae_iff.mpr (measure_mono_null (t := ({((lo : ℝ) : UnitAddCircle)} ∪
    {((-lo : ℝ) : UnitAddCircle)} : Set UnitAddCircle)) ?_
    (measure_union_null (volume_singleton_coe lo) (volume_singleton_coe (-lo))))
  · intro x hx
    obtain ⟨y, rfl⟩ := exists_real_coe x
    by_contra hcontra
    simp only [Set.mem_union, Set.mem_singleton_iff, not_or] at hcontra
    apply hx
    apply arc_difference_pointwise lo hi hlo hlh hhi y
    intro habs
    rcases (abs_eq hlo.le).mp habs with h | h
    · apply hcontra.1
      rw [← coe_sub_round_eq y, h]
    · apply hcontra.2
      rw [← coe_sub_round_eq y, h]

end Riesz1

end
end
