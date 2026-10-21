/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.GapLaw
public import Mathlib.Order.Fin.Tuple
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Cyclic changes of anchored coordinates

Reanchoring at the next particle is an affine transformation of the ordered
simplex of offsets. Its Jacobian has absolute value one.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

namespace Riesz1

/-- Anchored offsets after moving the anchor to the next particle. -/
def anchorCycle (n : ℕ) (y : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  Fin.snoc (fun i : Fin n => y i.succ - y 0) (1 - y 0)

lemma anchorCycle_castSucc (n : ℕ) (y : Fin (n + 1) → ℝ) (i : Fin n) :
    anchorCycle n y i.castSucc = y i.succ - y 0 := by
  simp [anchorCycle]

lemma anchorCycle_last (n : ℕ) (y : Fin (n + 1) → ℝ) :
    anchorCycle n y (Fin.last n) = 1 - y 0 := by
  simp [anchorCycle]

lemma measurePreserving_anchorCycle (n : ℕ) :
    MeasurePreserving (anchorCycle n) volume volume := by
  have hfirst := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have hlast := (volume_preserving_piFinSuccAbove
    (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).symm
  have hflip : MeasurePreserving (fun p : ℝ × (Fin n → ℝ) => (1 - p.1, p.2))
      (volume.prod volume) (volume.prod volume) :=
    (volume.measurePreserving_sub_left 1).prod (MeasurePreserving.id volume)
  convert hlast.comp (hflip.comp ((measurePreserving_shear n).comp hfirst)) using 1
  funext y i
  induction i using Fin.lastCases with
  | last =>
    simp [anchorCycle, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, sub_eq_add_neg]
  | cast i =>
    simp [anchorCycle, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.tail, sub_eq_add_neg]

lemma mem_anchoredDomain_anchorCycle_iff (n : ℕ) (y : Fin (n + 1) → ℝ) :
    anchorCycle n y ∈ anchoredDomain (n + 1) ↔ y ∈ anchoredDomain (n + 1) := by
  constructor
  · rintro ⟨hz, hm⟩
    have h0 : 0 < y 0 ∧ y 0 < 1 := by
      have h := hz (Fin.last n)
      rw [anchorCycle_last] at h
      constructor <;> linarith
    have htail : ∀ i : Fin n, y 0 < y i.succ ∧ y i.succ < 1 := by
      intro i
      have hp := (hz i.castSucc).1
      have hlt := hm (Fin.castSucc_lt_last i)
      rw [anchorCycle_castSucc] at hp
      rw [anchorCycle_castSucc, anchorCycle_last] at hlt
      constructor <;> linarith
    refine ⟨?_, ?_⟩
    · intro i
      induction i using Fin.cases with
      | zero => exact h0
      | succ i => exact ⟨lt_trans h0.1 (htail i).1, (htail i).2⟩
    · rw [← Fin.cons_self_tail y, Fin.strictMono_cons]
      refine ⟨fun i => (htail i).1, ?_⟩
      intro i j hij
      have h := hm (Fin.castSucc_lt_castSucc_iff.mpr hij)
      simp only [anchorCycle_castSucc] at h
      change y i.succ < y j.succ
      linarith
  · rintro ⟨hy, hm⟩
    refine ⟨?_, ?_⟩
    · intro i
      induction i using Fin.lastCases with
      | last =>
        rw [anchorCycle_last]
        constructor <;> linarith [(hy 0).1, (hy 0).2]
      | cast i =>
        rw [anchorCycle_castSucc]
        have hi := hm (Fin.succ_pos i)
        constructor <;> linarith [(hy 0).1, (hy i.succ).2]
    · intro i j hij
      induction j using Fin.lastCases with
      | last =>
        induction i using Fin.lastCases with
        | last => exact False.elim ((lt_irrefl _ ) hij)
        | cast i =>
          rw [anchorCycle_castSucc, anchorCycle_last]
          linarith [(hy i.succ).2]
      | cast j =>
        induction i using Fin.lastCases with
        | last => exact False.elim (not_lt_of_ge (Fin.le_last _) hij)
        | cast i =>
          rw [anchorCycle_castSucc, anchorCycle_castSucc]
          exact sub_lt_sub_right (hm (Fin.succ_lt_succ_iff.mpr
            (Fin.castSucc_lt_castSucc_iff.mp hij))) _

/-- Reanchoring preserves the Lebesgue measure on the ordered offset simplex. -/
lemma map_anchorCycle_restrict (n : ℕ) :
    (volume.restrict (anchoredDomain (n + 1))).map (anchorCycle n) =
      volume.restrict (anchoredDomain (n + 1)) := by
  have hT := measurePreserving_anchorCycle n
  ext B hB
  rw [Measure.map_apply hT.measurable hB, Measure.restrict_apply (hT.measurable hB),
    Measure.restrict_apply hB]
  have hset : anchorCycle n ⁻¹' B ∩ anchoredDomain (n + 1) =
      anchorCycle n ⁻¹' (B ∩ anchoredDomain (n + 1)) := by
    ext y
    simp only [mem_inter_iff, mem_preimage, mem_anchoredDomain_anchorCycle_iff]
  rw [hset]
  exact hT.measure_preimage
    (hB.inter (measurableSet_anchoredDomain _)).nullMeasurableSet

/-- Reanchoring rotates the circle-valued anchor vector and subtracts the new anchor. -/
lemma circle_anchorVector_anchorCycle (n : ℕ) (y : Fin (n + 1) → ℝ)
    (i : Fin (n + 2)) :
    ((@Fin.cons (n + 1) (fun _ => ℝ) 0 (anchorCycle n y) i : ℝ) : UnitAddCircle) =
      ((@Fin.cons (n + 1) (fun _ => ℝ) 0 y (finRotate (n + 2) i) : ℝ) : UnitAddCircle) - (y 0 : UnitAddCircle) := by
  induction i using Fin.cases with
  | zero =>
    rw [Fin.cons_zero, finRotate_apply_zero]
    change (0 : UnitAddCircle) = (y 0 : UnitAddCircle) - (y 0 : UnitAddCircle)
    simp
  | succ i =>
    rw [Fin.cons_succ]
    induction i using Fin.lastCases with
    | last =>
      rw [anchorCycle_last]
      have hr : finRotate (n + 2) (Fin.last n).succ = 0 := finRotate_last
      rw [hr, Fin.cons_zero, AddCircle.coe_sub, AddCircle.coe_period]
      simp
    | cast i =>
      rw [anchorCycle_castSucc]
      have hr : finRotate (n + 2) i.castSucc.succ = i.succ.succ := by
        apply Fin.ext
        rw [finRotate_of_lt (show (i.castSucc.succ : ℕ) < n + 1 by
          simp only [Fin.val_succ, Fin.val_castSucc]; omega)]
        rfl
      rw [hr, Fin.cons_succ, AddCircle.coe_sub]

/-- Reindexing an off-diagonal double sum by a permutation. -/
lemma sum_offDiagonal_equiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι ≃ ι) (f : ι → ι → ℝ) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, f (e i) (e j)) =
      ∑ i, ∑ j ∈ Finset.univ.erase i, f i j := by
  apply Fintype.sum_equiv e
  intro i
  exact Finset.sum_equiv e (fun j => by simp) (fun j _ => rfl)

/-- Internal reindexing lemma for energies of circle-valued anchor vectors. -/
lemma anchoredEnergy_eq_of_circle_perm (s : RieszExponent) (m : ℕ)
    (y z : Fin m → ℝ) (e : Equiv.Perm (Fin (m.succPNat : ℕ))) (a : UnitAddCircle)
    (h : ∀ i, (anchorVector z i : UnitAddCircle) =
      (anchorVector y (e i) : UnitAddCircle) - a) :
    anchoredEnergy s m z = anchoredEnergy s m y := by
  have hp (i j : Fin (m.succPNat : ℕ)) :
      rieszRepresentative s ((anchorVector z i - anchorVector z j : ℝ) : UnitAddCircle) =
        rieszRepresentative s
          ((anchorVector y (e i) - anchorVector y (e j) : ℝ) : UnitAddCircle) := by
    congr 1
    rw [AddCircle.coe_sub, h i, h j, AddCircle.coe_sub]
    abel
  unfold anchoredEnergy
  rw [show (∑ i : Fin (m.succPNat : ℕ), ∑ j ∈ Finset.univ.erase i,
      rieszRepresentative s ((anchorVector z i - anchorVector z j : ℝ) : UnitAddCircle)) =
      ∑ i : Fin (m.succPNat : ℕ), ∑ j ∈ Finset.univ.erase i,
        rieszRepresentative s
          ((anchorVector y (e i) - anchorVector y (e j) : ℝ) : UnitAddCircle) from
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hp i j]
  exact congrArg (fun t : ℝ => ((m.succPNat : ℕ) : ℝ) ^ (-s.val) * t)
    (sum_offDiagonal_equiv e (fun i j =>
      rieszRepresentative s ((anchorVector y i - anchorVector y j : ℝ) : UnitAddCircle)))

/-- The anchored energy is unchanged by cyclic reanchoring. -/
lemma anchoredEnergy_anchorCycle (s : RieszExponent) (n : ℕ) (y : Fin (n + 1) → ℝ) :
    anchoredEnergy s (n + 1) (anchorCycle n y) = anchoredEnergy s (n + 1) y := by
  apply anchoredEnergy_eq_of_circle_perm s (n + 1) y (anchorCycle n y)
    (finRotate (n + 2)) (y 0 : UnitAddCircle)
  intro i
  exact circle_anchorVector_anchorCycle n y i

/-- The anchored Gibbs law is invariant under cyclic reanchoring. -/
theorem map_anchorCycle_anchoredLaw (P : Parameters) (n : ℕ) :
    (anchoredLaw P (n + 1)).map (anchorCycle n) = anchoredLaw P (n + 1) := by
  have hT := (measurePreserving_anchorCycle n).measurable
  have hweight : (anchoredWeight P (n + 1)).map (anchorCycle n) =
      anchoredWeight P (n + 1) := by
    have hd : (fun y => anchoredDensity P (n + 1) (anchorCycle n y)) =
        anchoredDensity P (n + 1) := by
      funext y
      simp only [anchoredDensity, anchoredEnergy_anchorCycle]
    unfold anchoredWeight
    conv_lhs => rw [← hd]
    rw [map_withDensity_comp _ hT (measurable_anchoredDensity P _),
      map_anchorCycle_restrict]
  unfold anchoredLaw
  rw [Measure.map_smul _ hT.aemeasurable, hweight]

/-- The real cyclic offsets after reanchoring, for one period. -/
lemma anchoredCyclicOffset_anchorCycle_fin (n : ℕ) (y : Fin (n + 1) → ℝ)
    (i : Fin (n + 2)) :
    anchoredCyclicOffset (n + 1) (anchorCycle n y) (i : ℕ) =
      anchoredCyclicOffset (n + 1) y ((i : ℕ) + 1) - y 0 := by
  rw [anchoredCyclicOffset_natCast (n + 1) (anchorCycle n y) ⟨i.val, i.isLt⟩]
  change @Fin.cons (n + 1) (fun _ => ℝ) 0 (anchorCycle n y) i = _
  induction i using Fin.cases with
  | zero =>
    have h1 := anchoredCyclicOffset_natCast (n + 1) y (⟨1, by omega⟩ : Fin (n + 2))
    change anchoredCyclicOffset (n + 1) y 1 = y 0 at h1
    simp [h1]
  | succ i =>
    rw [Fin.cons_succ]
    induction i using Fin.lastCases with
    | last =>
      rw [anchorCycle_last]
      have hperiod := anchoredCyclicOffset_period (n + 1) y 0
      have hzero := anchoredCyclicOffset_natCast (n + 1) y 0
      change anchoredCyclicOffset (n + 1) y 0 = 0 at hzero
      simp only [zero_add, hzero, zero_add] at hperiod
      convert congrArg (fun t : ℝ => t - y 0) hperiod.symm using 1
      simp
    | cast i =>
      rw [anchorCycle_castSucc]
      have h := anchoredCyclicOffset_natCast (n + 1) y i.succ.succ
      change anchoredCyclicOffset (n + 1) y (i.succ.succ : ℕ) = y i.succ at h
      simpa only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one] using
        congrArg (fun t : ℝ => t - y 0) h.symm

/-- Reanchoring shifts every integer label by one. -/
lemma anchoredCyclicOffset_anchorCycle (n : ℕ) (y : Fin (n + 1) → ℝ) (j : ℤ) :
    anchoredCyclicOffset (n + 1) (anchorCycle n y) j =
      anchoredCyclicOffset (n + 1) y (j + 1) - y 0 := by
  obtain ⟨i, hi, q, rfl⟩ := exists_nat_add_mul (N := (n + 1).succPNat) j
  rw [anchoredCyclicOffset_add_mul]
  rw [show (i : ℤ) + ((n + 1).succPNat : ℕ) * q + 1 =
    ((i : ℤ) + 1) + ((n + 1).succPNat : ℕ) * q by ring,
    anchoredCyclicOffset_add_mul]
  have h := anchoredCyclicOffset_anchorCycle_fin n y ⟨i, hi⟩
  dsimp only at h
  rw [h]
  ring

lemma anchoredGapAt_anchorCycle (n : ℕ) (y : Fin (n + 1) → ℝ) (j : ℤ) :
    anchoredGapAt (n + 1) (anchorCycle n y) j = anchoredGapAt (n + 1) y (j + 1) := by
  simp only [anchoredGapAt, anchoredCyclicOffset_anchorCycle]
  ring

/-- The scalar gap law can be calculated by pushing forward the anchored law. -/
lemma map_gap_eq_map_anchoredGapAt (P : Parameters) (n : ℕ) (j : ℤ) :
    (gibbsMeasure P n.succPNat).map (fun X => gap X j) =
      (anchoredLaw P n).map (fun y => anchoredGapAt n y j) := by
  have hS : Measurable (fun X : Configuration n.succPNat => (anchorCoords n X.val).2) :=
    measurable_snd.comp (measurable_anchorCoords_config n)
  rw [← map_snd_gibbsMeasure P n,
    Measure.map_map (measurable_anchoredGapAt n j) hS]
  congr 1
  funext X
  exact gap_eq_anchoredGapAt n X j

/-- The same change of variables for an arbitrary family of integer gap labels. -/
lemma map_gapFamily_eq_map_anchoredGapAt {ι : Type*} (P : Parameters) (n : ℕ) (k : ι → ℤ) :
    (gibbsMeasure P n.succPNat).map (fun X i => gap X (k i)) =
      (anchoredLaw P n).map (fun y i => anchoredGapAt n y (k i)) := by
  have hS : Measurable (fun X : Configuration n.succPNat => (anchorCoords n X.val).2) :=
    measurable_snd.comp (measurable_anchorCoords_config n)
  have hG : Measurable (fun (y : Fin n → ℝ) i => anchoredGapAt n y (k i)) :=
    Measurable.of_eval fun i => measurable_anchoredGapAt n (k i)
  rw [← map_snd_gibbsMeasure P n, Measure.map_map hG hS]
  congr 1
  funext X i
  exact gap_eq_anchoredGapAt n X (k i)

/-- The joint gap law is invariant under cyclic shifts of all labels. -/
theorem map_gapFamily_add_one_gibbsMeasure {ι : Type*} (P : Parameters) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (k : ι → ℤ) :
    (gibbsMeasure P N).map (fun X i => gap X (k i + 1)) =
      (gibbsMeasure P N).map (fun X i => gap X (k i)) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = (n + 1).succPNat := by
    refine ⟨(N : ℕ) - 2, ?_⟩
    apply PNat.eq
    change (N : ℕ) = ((N : ℕ) - 2 + 1) + 1
    omega
  rw [map_gapFamily_eq_map_anchoredGapAt, map_gapFamily_eq_map_anchoredGapAt]
  have hG : Measurable (fun (y : Fin (n + 1) → ℝ) i => anchoredGapAt (n + 1) y (k i)) :=
    Measurable.of_eval fun i => measurable_anchoredGapAt (n + 1) (k i)
  have h := congrArg (Measure.map (fun y i => anchoredGapAt (n + 1) y (k i)))
    (map_anchorCycle_anchoredLaw P n)
  rw [Measure.map_map hG (measurePreserving_anchorCycle n).measurable] at h
  convert h using 1
  congr 1
  funext y i
  exact (anchoredGapAt_anchorCycle n y (k i)).symm

/-- Cyclic symmetry of every one-gap law, without any log-concavity assumption. -/
theorem map_gap_add_one_gibbsMeasure (P : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (j : ℤ) :
    (gibbsMeasure P N).map (fun X => gap X (j + 1)) =
      (gibbsMeasure P N).map (fun X => gap X j) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = (n + 1).succPNat := by
    refine ⟨(N : ℕ) - 2, ?_⟩
    apply PNat.eq
    change (N : ℕ) = ((N : ℕ) - 2 + 1) + 1
    omega
  rw [map_gap_eq_map_anchoredGapAt, map_gap_eq_map_anchoredGapAt]
  have h := congrArg (Measure.map (fun y => anchoredGapAt (n + 1) y j))
    (map_anchorCycle_anchoredLaw P n)
  rw [Measure.map_map (measurable_anchoredGapAt _ _)
    (measurePreserving_anchorCycle n).measurable] at h
  convert h using 1
  congr 1
  funext y
  exact (anchoredGapAt_anchorCycle n y j).symm

lemma gapVector_finRotate (N : ℕ+) (X : Configuration N) (i : Fin (N : ℕ)) :
    gapVector X (finRotate (N : ℕ) i) = gap X ((i : ℕ) + 1) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = n.succPNat :=
    ⟨N.natPred, (PNat.succPNat_natPred N).symm⟩
  unfold gapVector
  change gap X ((finRotate (n + 1) i : ℕ) : ℤ) = gap X ((i : ℕ) + 1)
  by_cases hi : i = Fin.last n
  · subst i
    rw [finRotate_last]
    simpa using (gap_add_N X 0).symm
  · have hr := coe_finRotate_of_ne_last hi
    simp only [hr, Nat.cast_add, Nat.cast_one]

/-- **Cyclic permutation invariance** of the full finite gap vector. -/
theorem map_gapVector_cycle_gibbsMeasure (P : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) :
    (gibbsMeasure P N).map (fun X i => gapVector X (finRotate (N : ℕ) i)) =
      (gibbsMeasure P N).map gapVector := by
  have h := map_gapFamily_add_one_gibbsMeasure P N hN (fun i : Fin (N : ℕ) => (i : ℕ))
  have heq : (fun (X : Configuration N) i => gapVector X (finRotate (N : ℕ) i)) =
      (fun (X : Configuration N) (i : Fin (N : ℕ)) => gap X ((i : ℕ) + 1)) := by
    funext X i
    exact gapVector_finRotate N X i
  rw [heq]
  exact h

end Riesz1

end
end
