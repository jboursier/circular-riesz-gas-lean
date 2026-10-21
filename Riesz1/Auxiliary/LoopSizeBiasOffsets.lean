/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopSizeBiasMarginal

/-!
# Recovering anchored offsets from microscopic gaps

The marginal clause of the size-bias part of Lemma 5.8.
The formulas are defined on their whole carriers. Their geometric assertions concern the
anchored simplex or the carrier without a particle at zero.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Riesz1

/-- Recover the ordered offsets from the microscopic gaps by finite partial sums. -/
def loopGapOffsets (N : ℕ+) (g : Fin (N : ℕ) → ℝ) : Fin ((N : ℕ) - 1) → ℝ :=
  fun i => (∑ r ∈ Finset.range (i.val + 1), gapOf g r) / (N : ℝ)

theorem measurable_loopGapOffsets (N : ℕ+) : Measurable (loopGapOffsets N) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro r _
  exact measurable_pi_apply _

/-- Partial gap sums recover the lifted distances from any integer-labeled particle. -/
theorem loopGapOffsets_shift (N : ℕ+) (X : Configuration N) (j : ℤ) :
    loopGapOffsets N (shiftFin N j (gapVector X)) =
      fun i => cyclicLift X (j + (i.val + 1 : ℕ)) - cyclicLift X j := by
  funext i
  unfold loopGapOffsets
  simp only [gapOf_shiftFin, ← gap_eq_gapOf_gapVector]
  rw [← blockLength_eq_sum, blockLength]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast N.ne_zero : (N : ℝ) ≠ 0)

/-- At label zero this is the original anchoring map. -/
theorem loopGapOffsets_gapVector (n : ℕ) (X : Configuration (n + 1).succPNat) :
    loopGapOffsets (n + 1).succPNat (gapVector X) = (anchorCoords (n + 1) X.val).2 := by
  rw [← shiftFin_zero (gapVector X), loopGapOffsets_shift]
  funext i
  have hi : (i.val + 1 : ℕ) < ((n + 1).succPNat : ℕ) := by
    have := i.isLt
    simp only [Nat.succPNat_coe] at *
    omega
  rw [zero_add, cyclicLift_natCast X ⟨i.val + 1, hi⟩, cyclicLift_zero]
  rfl

/-- The base gap law, pushed through partial sums, is exactly `P*`. -/
theorem map_loopGapOffsets (P : Parameters) (n : ℕ) :
    ((gibbsMeasure P (n + 1).succPNat).map gapVector).map (loopGapOffsets (n + 1).succPNat) =
      anchoredLaw P (n + 1) := by
  rw [Measure.map_map (measurable_loopGapOffsets _) (measurable_gapVector _)]
  have he : loopGapOffsets (n + 1).succPNat ∘ gapVector =
      fun X : Configuration (n + 1).succPNat => (anchorCoords (n + 1) X.val).2 :=
    funext (loopGapOffsets_gapVector n)
  rw [he]
  exact map_snd_gibbsMeasure P (n + 1)

/-- The preceding-particle probability is the restriction to the stated full-measure carrier. -/
def loopPrecedingMeasure (P : Parameters) (N : ℕ+) : Measure (LoopPrecedingConfiguration N) :=
  (gibbsMeasure P N).comap Subtype.val

theorem map_loopPrecedingMeasure (P : Parameters) (N : ℕ+) :
    (loopPrecedingMeasure P N).map Subtype.val = gibbsMeasure P N := by
  rw [loopPrecedingMeasure, map_comap_subtype_coe (measurableSet_loopPrecedingDomain N),
    Measure.restrict_eq_self_of_ae_mem (ae_loopPrecedingDomain P N)]

instance isProbabilityMeasure_loopPrecedingMeasure (P : Parameters) (N : ℕ+) :
    IsProbabilityMeasure (loopPrecedingMeasure P N) := by
  have := (modelWellDefined P N).2.2
  apply (Measure.isProbabilityMeasure_map_iff measurable_subtype_coe.aemeasurable).mp
  rw [map_loopPrecedingMeasure]
  infer_instance

/-- The finite preceding label and its integer lift give the same rooted gap vector. -/
theorem loopBoundaryGaps_preceding {N : ℕ+} (X : LoopPrecedingConfiguration N) :
    Internal.loopBoundaryGaps N X.val = shiftFin N (loopPrecedingLabel X) (gapVector X.val) := by
  obtain ⟨q, hq⟩ := (boundaryCyclicLabel_eq_iff N 0 0 X.val (boundaryCyclicLabel N 0 0 X.val)).mp rfl
  funext k
  change gapOf (gapVector X.val) ((boundaryCyclicLabel N 0 0 X.val : ℕ) + (k : ℕ)) =
    gapOf (gapVector X.val) (loopPrecedingLabel X + (k : ℕ))
  rw [← gap_eq_gapOf_gapVector, ← gap_eq_gapOf_gapVector]
  change _ = gap X.val (precedingLabel 0 0 X.val + (k : ℕ))
  rw [hq]
  unfold gap
  rw [show (boundaryCyclicLabel N 0 0 X.val : ℤ) + (N : ℕ) * q + (k : ℕ) =
      ((boundaryCyclicLabel N 0 0 X.val : ℤ) + (k : ℕ)) + (N : ℕ) * q by ring,
    show ((boundaryCyclicLabel N 0 0 X.val : ℤ) + (k : ℕ)) + (N : ℕ) * q + 1 =
      ((boundaryCyclicLabel N 0 0 X.val : ℤ) + (k : ℕ) + 1) + (N : ℕ) * q by ring,
    boundary_cyclicLift_add_mul, boundary_cyclicLift_add_mul]
  ring

theorem loopGapOffsets_preceding {N : ℕ+} (X : LoopPrecedingConfiguration N) :
    loopGapOffsets N (Internal.loopBoundaryGaps N X.val) = loopPrecedingOffsets X := by
  rw [loopBoundaryGaps_preceding, loopGapOffsets_shift]
  rfl

theorem measurable_loopPrecedingOffsets (N : ℕ+) :
    Measurable (loopPrecedingOffsets (N := N)) := by
  have h : Measurable (fun X : LoopPrecedingConfiguration N =>
      loopGapOffsets N (Internal.loopBoundaryGaps N X.val)) := (measurable_loopGapOffsets N).comp
    ((Internal.measurable_loopBoundaryGaps N).comp measurable_subtype_coe)
  simpa only [Function.comp_def, loopGapOffsets_preceding] using h

theorem measurable_loopPrecedingLabel (N : ℕ+) : Measurable (loopPrecedingLabel (N := N)) :=
  (measurable_precedingLabel 0 0).comp measurable_subtype_coe

/-- The full rooted vector is the zero anchor followed by the preceding offsets. -/
theorem loopPrecedingY_eq_anchorVector (n : ℕ) (X : LoopPrecedingConfiguration (n + 1).succPNat) :
    loopPrecedingY X = anchorVector (loopPrecedingOffsets X) := by
  funext i
  induction i using Fin.cases with
  | zero =>
    simp only [loopPrecedingY, Fin.val_zero, Nat.cast_zero, add_zero, sub_self]
    exact (anchorVector_zero _).symm
  | succ i => rfl

theorem measurable_loopPrecedingY (n : ℕ) :
    Measurable (loopPrecedingY (N := (n + 1).succPNat)) := by
  have h := (measurable_anchorVector (n + 1)).comp (measurable_loopPrecedingOffsets (n + 1).succPNat)
  have he : loopPrecedingY (N := (n + 1).succPNat) =
      (fun X => anchorVector (loopPrecedingOffsets X)) := funext (loopPrecedingY_eq_anchorVector n)
  rw [he]
  exact h

/-- The microscopic first gap of the rooted coordinates is exactly `w`. -/
theorem loopSizeWeight_preceding (n : ℕ) (X : LoopPrecedingConfiguration (n + 1).succPNat) :
    loopSizeWeight n (loopPrecedingOffsets X) = gap X.val (loopPrecedingLabel X) := by
  rfl

/-- The strict displacement interval. -/
theorem loopPrecedingD_mem_weight (n : ℕ) (X : LoopPrecedingConfiguration (n + 1).succPNat) :
    0 < loopPrecedingD X ∧ loopPrecedingD X < loopSizeWeight n (loopPrecedingOffsets X) := by
  rw [loopSizeWeight_preceding]
  exact loopPrecedingD_mem X

/-- Measurability of the microscopic displacement on its actual carrier. -/
theorem measurable_loopPrecedingD (N : ℕ+) : Measurable (loopPrecedingD (N := N)) := by
  have hm : Measurable (fun p : Configuration N × ℤ => cyclicLift p.1 p.2) :=
    measurable_from_prod_countable_left fun j => measurable_cyclicLift j
  exact (hm.comp (measurable_subtype_coe.prodMk
    ((measurable_precedingLabel 0 0).comp measurable_subtype_coe))).const_mul _

/-- Push the size-biased gap law through the partial sums. -/
theorem map_loopGapOffsets_sizeBiased (P : Parameters) (n : ℕ) :
    (((gibbsMeasure P (n + 1).succPNat).map gapVector).withDensity
      (fun g => ENNReal.ofReal (g ⟨0, (n + 1).succPNat.pos⟩))).map
        (loopGapOffsets (n + 1).succPNat) = loopSizeBiasedLaw P n := by
  have hmG : Measurable (fun g : Fin (((n + 1).succPNat : ℕ)) → ℝ =>
      ENNReal.ofReal (loopSizeWeight n (loopGapOffsets (n + 1).succPNat g))) :=
    (measurable_loopSizeWeight n).ennreal_ofReal.comp (measurable_loopGapOffsets _)
  have hw : (fun g => ENNReal.ofReal (g ⟨0, (n + 1).succPNat.pos⟩)) =ᵐ[
      (gibbsMeasure P (n + 1).succPNat).map gapVector]
      (fun g => ENNReal.ofReal (loopSizeWeight n (loopGapOffsets (n + 1).succPNat g))) := by
    apply (ae_map_iff (measurable_gapVector _).aemeasurable
      (measurableSet_eq_fun (measurable_pi_apply _).ennreal_ofReal hmG)).mpr
    exact ae_of_all _ fun X => by
      have he := congrArg (fun y : Fin (n + 1) → ℝ => ENNReal.ofReal (loopSizeWeight n y))
        (loopGapOffsets_gapVector n X)
      exact (congrArg ENNReal.ofReal (loopSizeWeight_anchorCoords n X)).symm.trans he.symm
  rw [withDensity_congr_ae hw]
  have he := map_withDensity_comp ((gibbsMeasure P (n + 1).succPNat).map gapVector)
    (F := fun g => (loopGapOffsets (n + 1).succPNat g : Fin (n + 1) → ℝ))
    (measurable_loopGapOffsets _) (measurable_loopSizeWeight n).ennreal_ofReal
  exact he.trans (congrArg (fun μ : Measure (Fin (n + 1) → ℝ) =>
    μ.withDensity (fun y => ENNReal.ofReal (loopSizeWeight n y))) (map_loopGapOffsets P n))

/-- The size-bias part of Lemma 5.8, the marginal law: the preceding-particle
anchored vector has law `w P*`, on the full-measure carrier of the preceding-particle variables. -/
theorem map_loopPrecedingOffsets (P : Parameters) (n : ℕ) :
    (loopPrecedingMeasure P (n + 1).succPNat).map loopPrecedingOffsets = loopSizeBiasedLaw P n := by
  have hm : Measurable (fun X : Configuration (n + 1).succPNat =>
      loopGapOffsets (n + 1).succPNat (Internal.loopBoundaryGaps (n + 1).succPNat X)) :=
    (measurable_loopGapOffsets _).comp (Internal.measurable_loopBoundaryGaps _)
  calc
    _ = ((loopPrecedingMeasure P (n + 1).succPNat).map Subtype.val).map
        (fun X => loopGapOffsets (n + 1).succPNat (Internal.loopBoundaryGaps _ X)) := by
      rw [Measure.map_map hm measurable_subtype_coe]
      congr 1
      funext X
      exact (loopGapOffsets_preceding X).symm
    _ = ((gibbsMeasure P (n + 1).succPNat).map (Internal.loopBoundaryGaps _)).map
        (loopGapOffsets (n + 1).succPNat) := by
      rw [map_loopPrecedingMeasure,
        Measure.map_map (measurable_loopGapOffsets _) (Internal.measurable_loopBoundaryGaps _)]
      rfl
    _ = _ := by
      rw [Internal.map_loopBoundaryGaps P _ (by simp)]
      exact map_loopGapOffsets_sizeBiased P n

end Riesz1

end
