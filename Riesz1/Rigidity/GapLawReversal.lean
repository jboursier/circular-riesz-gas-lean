/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.GapLawSymmetry

/-!
# Reversal of cyclic order

Reflection about the anchor reverses the order of the offsets, sending
`yᵢ` to `1 - y_{n-1-i}`. It preserves the ordered simplex, Lebesgue measure,
and the Gibbs energy. On integer gap labels it acts by `j ↦ -j-1`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

namespace Riesz1

/-- Anchored particle offsets after reversing the cyclic orientation. -/
def anchorReverse (n : ℕ) (y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => 1 - y i.rev

lemma anchorReverse_involutive (n : ℕ) : Function.Involutive (anchorReverse n) := by
  intro y
  funext i
  simp [anchorReverse]

lemma measurePreserving_anchorReverse (n : ℕ) :
    MeasurePreserving (anchorReverse n) volume volume := by
  have hp := volume_measurePreserving_piCongrLeft (fun _ : Fin n => ℝ) (Fin.revPerm (n := n))
  have hr : MeasurePreserving (fun y : Fin n → ℝ => fun i => 1 - y i) volume volume :=
    volume_preserving_pi (fun _ => volume.measurePreserving_sub_left 1)
  convert hr.comp hp using 1
  funext y i
  have h := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin n => ℝ)
    (Fin.revPerm (n := n)) y i.rev
  simpa [anchorReverse] using congrArg (fun t : ℝ => 1 - t) h.symm

lemma anchorReverse_mem_anchoredDomain (n : ℕ) {y : Fin n → ℝ}
    (hy : y ∈ anchoredDomain n) : anchorReverse n y ∈ anchoredDomain n := by
  refine ⟨?_, ?_⟩
  · intro i
    dsimp only [anchorReverse]
    constructor <;> linarith [(hy.1 i.rev).1, (hy.1 i.rev).2]
  · intro i j hij
    have h := hy.2 (Fin.rev_lt_rev.mpr hij)
    dsimp only [anchorReverse]
    linarith

lemma mem_anchoredDomain_anchorReverse_iff (n : ℕ) (y : Fin n → ℝ) :
    anchorReverse n y ∈ anchoredDomain n ↔ y ∈ anchoredDomain n := by
  constructor
  · intro hy
    have h := anchorReverse_mem_anchoredDomain n hy
    rwa [anchorReverse_involutive] at h
  · exact anchorReverse_mem_anchoredDomain n

lemma map_anchorReverse_restrict (n : ℕ) :
    (volume.restrict (anchoredDomain n)).map (anchorReverse n) =
      volume.restrict (anchoredDomain n) := by
  have hT := measurePreserving_anchorReverse n
  ext B hB
  rw [Measure.map_apply hT.measurable hB, Measure.restrict_apply (hT.measurable hB),
    Measure.restrict_apply hB]
  have hset : anchorReverse n ⁻¹' B ∩ anchoredDomain n =
      anchorReverse n ⁻¹' (B ∩ anchoredDomain n) := by
    ext y
    simp only [mem_inter_iff, mem_preimage, mem_anchoredDomain_anchorReverse_iff]
  rw [hset]
  exact hT.measure_preimage (hB.inter (measurableSet_anchoredDomain n)).nullMeasurableSet

/-- Reversal of particle labels fixing the anchor. -/
def anchorReverseIndex (n : ℕ) : Fin (n + 1) → Fin (n + 1) :=
  Fin.cases 0 (fun i => i.rev.succ)

lemma anchorReverseIndex_involutive (n : ℕ) : Function.Involutive (anchorReverseIndex n) := by
  intro i
  induction i using Fin.cases with
  | zero => simp [anchorReverseIndex]
  | succ i => simp [anchorReverseIndex]

/-- The permutation of particle labels induced by orientation reversal. -/
def anchorReversePerm (n : ℕ) : Equiv.Perm (Fin (n + 1)) :=
  { toFun := anchorReverseIndex n
    invFun := anchorReverseIndex n
    left_inv := anchorReverseIndex_involutive n
    right_inv := anchorReverseIndex_involutive n }

lemma anchorReversePerm_apply (n : ℕ) (i : Fin (n + 1)) :
    anchorReversePerm n i = anchorReverseIndex n i := rfl

lemma circle_anchorVector_anchorReverse (n : ℕ) (y : Fin n → ℝ) (i : Fin (n + 1)) :
    ((@Fin.cons n (fun _ => ℝ) 0 (anchorReverse n y) i : ℝ) : UnitAddCircle) =
      -((@Fin.cons n (fun _ => ℝ) 0 y (anchorReversePerm n i) : ℝ) : UnitAddCircle) := by
  induction i using Fin.cases with
  | zero => simp [anchorReversePerm_apply, anchorReverseIndex]
  | succ i =>
    simp only [Fin.cons_succ, anchorReversePerm_apply, 
      anchorReverseIndex, Fin.cases_succ, anchorReverse, AddCircle.coe_sub,
      AddCircle.coe_period, zero_sub]

lemma rieszRepresentative_neg (s : RieszExponent) (u : UnitAddCircle) :
    rieszRepresentative s (-u) = rieszRepresentative s u := by
  simp only [rieszRepresentative, HurwitzZeta.hurwitzZetaEven_neg]

lemma anchoredEnergy_anchorReverse (s : RieszExponent) (n : ℕ) (y : Fin n → ℝ) :
    anchoredEnergy s n (anchorReverse n y) = anchoredEnergy s n y := by
  have hp (i j : Fin (n.succPNat : ℕ)) :
      rieszRepresentative s ((anchorVector (anchorReverse n y) i -
        anchorVector (anchorReverse n y) j : ℝ) : UnitAddCircle) =
      rieszRepresentative s ((anchorVector y (anchorReversePerm n i) -
        anchorVector y (anchorReversePerm n j) : ℝ) : UnitAddCircle) := by
    have hi := circle_anchorVector_anchorReverse n y i
    have hj := circle_anchorVector_anchorReverse n y j
    change (anchorVector (anchorReverse n y) i : UnitAddCircle) =
      -(anchorVector y (anchorReversePerm n i) : UnitAddCircle) at hi
    change (anchorVector (anchorReverse n y) j : UnitAddCircle) =
      -(anchorVector y (anchorReversePerm n j) : UnitAddCircle) at hj
    rw [AddCircle.coe_sub, hi, hj]
    rw [show -(anchorVector y (anchorReversePerm n i) : UnitAddCircle) -
        -(anchorVector y (anchorReversePerm n j) : UnitAddCircle) =
        -((anchorVector y (anchorReversePerm n i) -
          anchorVector y (anchorReversePerm n j) : ℝ) : UnitAddCircle) by
      rw [AddCircle.coe_sub]; abel]
    exact rieszRepresentative_neg s _
  unfold anchoredEnergy
  congr 1
  calc
    _ = ∑ i : Fin (n.succPNat : ℕ), ∑ j ∈ Finset.univ.erase i,
        rieszRepresentative s ((anchorVector y (anchorReversePerm n i) -
          anchorVector y (anchorReversePerm n j) : ℝ) : UnitAddCircle) :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hp i j
    _ = _ := sum_offDiagonal_equiv (anchorReversePerm n) (fun i j =>
      rieszRepresentative s ((anchorVector y i - anchorVector y j : ℝ) : UnitAddCircle))

theorem map_anchorReverse_anchoredLaw (P : Parameters) (n : ℕ) :
    (anchoredLaw P n).map (anchorReverse n) = anchoredLaw P n := by
  have hT := (measurePreserving_anchorReverse n).measurable
  have hweight : (anchoredWeight P n).map (anchorReverse n) = anchoredWeight P n := by
    have hd : (fun y => anchoredDensity P n (anchorReverse n y)) = anchoredDensity P n := by
      funext y
      simp only [anchoredDensity, anchoredEnergy_anchorReverse]
    unfold anchoredWeight
    conv_lhs => rw [← hd]
    rw [map_withDensity_comp _ hT (measurable_anchoredDensity P n), map_anchorReverse_restrict]
  unfold anchoredLaw
  rw [Measure.map_smul _ hT.aemeasurable, hweight]

lemma anchoredCyclicOffset_anchorReverse_fin (n : ℕ) (y : Fin n → ℝ) (i : Fin (n + 1)) :
    anchoredCyclicOffset n (anchorReverse n y) (i : ℕ) =
      -anchoredCyclicOffset n y (-((i : ℕ) : ℤ)) := by
  rw [anchoredCyclicOffset_natCast n (anchorReverse n y) ⟨i.val, i.isLt⟩]
  change @Fin.cons n (fun _ => ℝ) 0 (anchorReverse n y) i = _
  induction i using Fin.cases with
  | zero =>
    have h := anchoredCyclicOffset_natCast n y 0
    change anchoredCyclicOffset n y 0 = 0 at h
    simp [h]
  | succ i =>
    have hidx : -((i.succ : ℕ) : ℤ) = (i.rev.succ : ℕ) + (n.succPNat : ℕ) * (-1 : ℤ) := by
      simp only [Fin.val_succ, Fin.val_rev, Nat.succPNat_coe, Nat.cast_succ]
      omega
    rw [hidx, anchoredCyclicOffset_add_mul,
      anchoredCyclicOffset_natCast n y ⟨i.rev.succ.val, i.rev.succ.isLt⟩]
    change 1 - y i.rev = -(y i.rev + (-1 : ℤ))
    push_cast
    ring

lemma anchoredCyclicOffset_anchorReverse (n : ℕ) (y : Fin n → ℝ) (j : ℤ) :
    anchoredCyclicOffset n (anchorReverse n y) j = -anchoredCyclicOffset n y (-j) := by
  obtain ⟨i, hi, q, rfl⟩ := exists_nat_add_mul (N := n.succPNat) j
  rw [anchoredCyclicOffset_add_mul]
  rw [show -((i : ℤ) + (n.succPNat : ℕ) * q) =
    -(i : ℤ) + (n.succPNat : ℕ) * (-q) by ring, anchoredCyclicOffset_add_mul]
  have h := anchoredCyclicOffset_anchorReverse_fin n y ⟨i, hi⟩
  dsimp only at h
  rw [h]
  push_cast
  ring

lemma anchoredGapAt_anchorReverse (n : ℕ) (y : Fin n → ℝ) (j : ℤ) :
    anchoredGapAt n (anchorReverse n y) j = anchoredGapAt n y (-j - 1) := by
  simp only [anchoredGapAt, anchoredCyclicOffset_anchorReverse]
  rw [show -j - 1 + 1 = -j by ring, show -(j + 1) = -j - 1 by ring]
  ring

/-- Reversal invariance of the entire gap law, for arbitrary integer label families. -/
theorem map_gapFamily_reverse_gibbsMeasure {ι : Type*} (P : Parameters) (N : ℕ+) (k : ι → ℤ) :
    (gibbsMeasure P N).map (fun X i => gap X (-k i - 1)) =
      (gibbsMeasure P N).map (fun X i => gap X (k i)) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = n.succPNat :=
    ⟨N.natPred, (PNat.succPNat_natPred N).symm⟩
  rw [map_gapFamily_eq_map_anchoredGapAt, map_gapFamily_eq_map_anchoredGapAt]
  have hG : Measurable (fun (y : Fin n → ℝ) i => anchoredGapAt n y (k i)) :=
    Measurable.of_eval fun i => measurable_anchoredGapAt n (k i)
  have h := congrArg (Measure.map (fun y i => anchoredGapAt n y (k i)))
    (map_anchorReverse_anchoredLaw P n)
  rw [Measure.map_map hG (measurePreserving_anchorReverse n).measurable] at h
  convert h using 1
  congr 1
  funext y i
  exact (anchoredGapAt_anchorReverse n y (k i)).symm

lemma gapVector_rev (N : ℕ+) (X : Configuration N) (i : Fin (N : ℕ)) :
    gapVector X i.rev = gap X (-((i : ℕ) : ℤ) - 1) := by
  have hidx : -((i : ℕ) : ℤ) - 1 + (N : ℕ) = ((i.rev : ℕ) : ℤ) := by
    simp only [Fin.val_rev]
    have := i.isLt
    omega
  unfold gapVector
  rw [← hidx, gap_add_N]

/-- **Reversal invariance** of the full finite gap vector. -/
theorem map_gapVector_reverse_gibbsMeasure (P : Parameters) (N : ℕ+) :
    (gibbsMeasure P N).map (fun X i => gapVector X i.rev) =
      (gibbsMeasure P N).map gapVector := by
  have h := map_gapFamily_reverse_gibbsMeasure P N (fun i : Fin (N : ℕ) => (i : ℕ))
  have heq : (fun (X : Configuration N) i => gapVector X i.rev) =
      (fun (X : Configuration N) (i : Fin (N : ℕ)) => gap X (-((i : ℕ) : ℤ) - 1)) := by
    funext X i
    exact gapVector_rev N X i
  rw [heq]
  exact h

end Riesz1

end
end
