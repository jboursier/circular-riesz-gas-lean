/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Gibbs.FluctuationMoments
public import Riesz1.Rigidity.Inversion

/-!
# Rotation and gaps under the Gibbs measure

The rotation part of Lemma 4.2. The common uniform
rotation remains independent of the anchored coordinates after a shift depending on
those coordinates. In particular every cyclic particle rotation is independent of
the entire gap vector.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

namespace Riesz1

/-- The vector of all nearest-neighbor gaps, with one complete period of labels. -/
def gapVector {N : ℕ+} (X : Configuration N) : Fin (N : ℕ) → ℝ :=
  fun i => gap X (i : ℕ)

lemma measurable_gapVector (N : ℕ+) : Measurable (@gapVector N) :=
  Measurable.of_eval fun i => measurable_gap (i : ℕ)

/-- The anchored offset at an arbitrary integer label, including its winding number. -/
def anchoredCyclicOffset (n : ℕ) (y : Fin n → ℝ) (j : ℤ) : ℝ :=
  anchorVector y ⟨(j % (n.succPNat : ℕ)).toNat, by
    have h := Int.emod_lt_of_pos j
      (show (0 : ℤ) < (n.succPNat : ℕ) by exact_mod_cast n.succPNat.pos)
    exact_mod_cast (Int.toNat_lt (Int.emod_nonneg j
      (by exact_mod_cast n.succPNat.ne_zero))).mpr h⟩ +
    (j / (n.succPNat : ℕ) : ℤ)

lemma measurable_anchoredCyclicOffset (n : ℕ) (j : ℤ) :
    Measurable (fun y : Fin n → ℝ => anchoredCyclicOffset n y j) := by
  unfold anchoredCyclicOffset
  exact (((measurable_pi_apply _).comp (measurable_anchorVector n))).add_const _

lemma cyclicLift_eq_anchor_add (n : ℕ) (X : Configuration n.succPNat) (j : ℤ) :
    cyclicLift X j = X.val 0 + anchoredCyclicOffset n (anchorCoords n X.val).2 j := by
  unfold cyclicLift anchoredCyclicOffset
  rw [apply_eq_anchor_add n X.val]
  ring

lemma anchoredCyclicOffset_natCast (n : ℕ) (y : Fin n → ℝ)
    (i : Fin (n.succPNat : ℕ)) :
    anchoredCyclicOffset n y (i : ℕ) = anchorVector y i := by
  have hi0 : (0 : ℤ) ≤ (i : ℕ) := by positivity
  have hiN : ((i : ℕ) : ℤ) < (n.succPNat : ℕ) := by exact_mod_cast i.isLt
  unfold anchoredCyclicOffset
  simp only [Int.emod_eq_of_lt hi0 hiN, Int.ediv_eq_zero_of_lt hi0 hiN,
    Int.toNat_natCast, Int.cast_zero, add_zero]

lemma anchoredCyclicOffset_add_mul (n : ℕ) (y : Fin n → ℝ) (j q : ℤ) :
    anchoredCyclicOffset n y (j + (n.succPNat : ℕ) * q) =
      anchoredCyclicOffset n y j + q := by
  have hN : ((n.succPNat : ℕ) : ℤ) ≠ 0 := by exact_mod_cast n.succPNat.ne_zero
  unfold anchoredCyclicOffset
  simp only [Int.add_mul_emod_self_left, Int.add_mul_ediv_left _ _ hN]
  push_cast
  ring

lemma anchoredCyclicOffset_period (n : ℕ) (y : Fin n → ℝ) (j : ℤ) :
    anchoredCyclicOffset n y (j + (n.succPNat : ℕ)) =
      anchoredCyclicOffset n y j + 1 := by
  simpa using anchoredCyclicOffset_add_mul n y j 1

/-- The gap at an arbitrary integer label, expressed in anchored coordinates. -/
def anchoredGapAt (n : ℕ) (y : Fin n → ℝ) (j : ℤ) : ℝ :=
  (n + 1 : ℝ) * (anchoredCyclicOffset n y (j + 1) - anchoredCyclicOffset n y j)

lemma measurable_anchoredGapAt (n : ℕ) (j : ℤ) :
    Measurable (fun y : Fin n → ℝ => anchoredGapAt n y j) :=
  measurable_const.mul ((measurable_anchoredCyclicOffset n _).sub
    (measurable_anchoredCyclicOffset n _))

lemma gap_eq_anchoredGapAt (n : ℕ) (X : Configuration n.succPNat) (j : ℤ) :
    gap X j = anchoredGapAt n (anchorCoords n X.val).2 j := by
  simp only [gap, anchoredGapAt, cyclicLift_eq_anchor_add, Nat.succPNat_coe, Nat.cast_succ]
  ring

/-- Gaps computed from anchored offsets, on the entire ambient coordinate space. -/
def anchoredGapVector (n : ℕ) (y : Fin n → ℝ) : Fin (n.succPNat : ℕ) → ℝ :=
  fun i => (n + 1 : ℝ) *
    (anchoredCyclicOffset n y ((i : ℕ) + 1) - anchoredCyclicOffset n y (i : ℕ))

lemma measurable_anchoredGapVector (n : ℕ) : Measurable (anchoredGapVector n) := by
  refine Measurable.of_eval fun i => ?_
  exact measurable_const.mul ((measurable_anchoredCyclicOffset n _).sub
    (measurable_anchoredCyclicOffset n _))

lemma gapVector_eq_anchoredGapVector (n : ℕ) (X : Configuration n.succPNat) :
    gapVector X = anchoredGapVector n (anchorCoords n X.val).2 := by
  funext i
  simp only [gapVector, gap, anchoredGapVector, cyclicLift_eq_anchor_add]
  simp only [Nat.succPNat_coe, Nat.cast_succ]
  ring

/-- A uniform circle rotation shifted by an independent measurable offset has a product
law with the original offset variable. -/
lemma map_uniform_shift_joint {n : ℕ} (a : (Fin n → ℝ) → ℝ) (ha : Measurable a)
    (ν : Measure (Fin n → ℝ)) [IsProbabilityMeasure ν] :
    ((volume.restrict (Ico (0 : ℝ) 1)).prod ν).map
      (fun p : ℝ × (Fin n → ℝ) => (((p.1 + a p.2 : ℝ) : UnitAddCircle), p.2)) =
      (volume : Measure UnitAddCircle).prod ν := by
  have hskew : MeasurePreserving
      (fun p : (Fin n → ℝ) × ℝ => (p.1, ((p.2 + a p.1 : ℝ) : UnitAddCircle)))
      (ν.prod (volume.restrict (Ico (0 : ℝ) 1))) (ν.prod volume) := by
    refine (MeasurePreserving.id ν).skew_product
      (μc := volume.restrict (Ico (0 : ℝ) 1)) (μd := (volume : Measure UnitAddCircle))
      (g := fun y t => ((t + a y : ℝ) : UnitAddCircle)) ?_ ?_
    · exact measurable_coe_circle.comp (measurable_snd.add (ha.comp measurable_fst))
    · exact ae_of_all _ fun y => map_circle_translate_uniform (a y)
  exact ((Measure.measurePreserving_swap).comp
    (hskew.comp (Measure.measurePreserving_swap))).map_eq

/-- Every cyclic particle rotation is uniform, jointly with the independent anchored vector. -/
theorem map_cyclicLift_anchorCoords_gibbsMeasure (P : Parameters) (n : ℕ) (j : ℤ) :
    (gibbsMeasure P n.succPNat).map
      (fun X : Configuration n.succPNat =>
        ((cyclicLift X j : UnitAddCircle), (anchorCoords n X.val).2)) =
      (volume : Measure UnitAddCircle).prod (anchoredLaw P n) := by
  have := isProbabilityMeasure_anchoredLaw P n
  have hF : Measurable (fun p : ℝ × (Fin n → ℝ) =>
      (((p.1 + anchoredCyclicOffset n p.2 j : ℝ) : UnitAddCircle), p.2)) :=
    (measurable_coe_circle.comp (measurable_fst.add
      ((measurable_anchoredCyclicOffset n j).comp measurable_snd))).prodMk measurable_snd
  have hfun : (fun X : Configuration n.succPNat =>
      ((cyclicLift X j : UnitAddCircle), (anchorCoords n X.val).2)) =
      (fun p : ℝ × (Fin n → ℝ) =>
        (((p.1 + anchoredCyclicOffset n p.2 j : ℝ) : UnitAddCircle), p.2)) ∘
      (fun X : Configuration n.succPNat => anchorCoords n X.val) := by
    funext X
    simp only [Function.comp_apply, anchorCoords, cyclicLift_eq_anchor_add]
  rw [hfun, ← Measure.map_map hF (measurable_anchorCoords_config n),
    map_gibbsMeasure_anchorCoords]
  exact map_uniform_shift_joint _ (measurable_anchoredCyclicOffset n j) _

/-- Every integer-labeled particle rotation has uniform Haar law. -/
theorem map_cyclicLift_gibbsMeasure (P : Parameters) (N : ℕ+) (j : ℤ) :
    (gibbsMeasure P N).map (fun X : Configuration N => (cyclicLift X j : UnitAddCircle)) =
      volume := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = n.succPNat :=
    ⟨N.natPred, (PNat.succPNat_natPred N).symm⟩
  have := isProbabilityMeasure_anchoredLaw P n
  have h := congrArg (Measure.map Prod.fst) (map_cyclicLift_anchorCoords_gibbsMeasure P n j)
  have hJ : Measurable (fun X : Configuration n.succPNat =>
      ((cyclicLift X j : UnitAddCircle), (anchorCoords n X.val).2)) := by
    exact (measurable_coe_circle.comp (measurable_cyclicLift j)).prodMk
      (measurable_snd.comp (measurable_anchorCoords_config n))
  rw [Measure.map_map measurable_fst hJ,
    Measure.map_fst_prod, measure_univ, one_smul] at h
  exact h

/-- The joint law of any particle rotation and all the gaps is a product. -/
theorem map_cyclicLift_gapVector_gibbsMeasure (P : Parameters) (N : ℕ+) (j : ℤ) :
    (gibbsMeasure P N).map (fun X : Configuration N =>
      ((cyclicLift X j : UnitAddCircle), gapVector X)) =
      (volume : Measure UnitAddCircle).prod ((gibbsMeasure P N).map gapVector) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = n.succPNat :=
    ⟨N.natPred, (PNat.succPNat_natPred N).symm⟩
  have := isProbabilityMeasure_anchoredLaw P n
  have hmap : (gibbsMeasure P n.succPNat).map gapVector =
      (anchoredLaw P n).map (anchoredGapVector n) := by
    have hS : Measurable (fun X : Configuration n.succPNat => (anchorCoords n X.val).2) :=
      measurable_snd.comp (measurable_anchorCoords_config n)
    rw [← map_snd_gibbsMeasure P n,
      Measure.map_map (measurable_anchoredGapVector n) hS]
    congr 1
    funext X
    exact gapVector_eq_anchoredGapVector n X
  have h := congrArg (Measure.map (Prod.map (id : UnitAddCircle → UnitAddCircle)
      (anchoredGapVector n))) (map_cyclicLift_anchorCoords_gibbsMeasure P n j)
  have hJ : Measurable (fun X : Configuration n.succPNat =>
      ((cyclicLift X j : UnitAddCircle), (anchorCoords n X.val).2)) := by
    exact (measurable_coe_circle.comp (measurable_cyclicLift j)).prodMk
      (measurable_snd.comp (measurable_anchorCoords_config n))
  rw [Measure.map_map (measurable_id.prodMap (measurable_anchoredGapVector n)) hJ,
    ← Measure.map_prod_map _ _ measurable_id (measurable_anchoredGapVector n),
    Measure.map_id, ← hmap] at h
  convert h using 1
  congr 1
  funext X
  exact Prod.ext rfl (gapVector_eq_anchoredGapVector n X)

/-- **Rotation independence**, item 1 of Lemma 4.2. -/
theorem indepFun_cyclicLift_gapVector (P : Parameters) (N : ℕ+) (j : ℤ) :
    IndepFun (fun X : Configuration N => (cyclicLift X j : UnitAddCircle)) gapVector
      (gibbsMeasure P N) := by
  have := (modelWellDefined P N).2.2
  have hR : Measurable (fun X : Configuration N => (cyclicLift X j : UnitAddCircle)) :=
    measurable_coe_circle.comp (measurable_cyclicLift j)
  rw [indepFun_iff_map_prod_eq_prod_map_map hR.aemeasurable
    (measurable_gapVector N).aemeasurable, map_cyclicLift_gibbsMeasure]
  exact map_cyclicLift_gapVector_gibbsMeasure P N j

end Riesz1

end
end
