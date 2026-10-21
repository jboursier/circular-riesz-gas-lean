/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.BoundarySelectionLawBounds
public import Riesz1.Rigidity.RigidityGaps

/-!
# Boundary-selected block deviations

Internal assembly lemmas for the proof of Theorem 1.
The sum of consecutive entries of a gap vector defines a Borel cyclic event
family, to which the boundary selection estimate applies.
-/

public section

noncomputable section

open MeasureTheory Finset Fin.NatCast

namespace Riesz1.Internal

/-- The sum of `k` consecutive coordinates of a cyclic gap vector. -/
def rigidityBlockSum (N : ℕ+) (y : Fin (N : ℕ) → ℝ) (i : Fin (N : ℕ)) (k : ℕ) : ℝ :=
  haveI : NeZero (N : ℕ) := ⟨N.ne_zero⟩
  ∑ r ∈ range k, y (i + (↑r : Fin (N : ℕ)))

theorem rigidity_gap_add_mul {N : ℕ+} (X : Configuration N) (j q : ℤ) :
    gap X (j + (N : ℕ) * q) = gap X j := by
  unfold gap
  rw [show j + (N : ℕ) * q + 1 = (j + 1) + (N : ℕ) * q by ring,
    boundary_cyclicLift_add_mul, boundary_cyclicLift_add_mul]
  ring

theorem rigidity_gap_nat_mod {N : ℕ+} (X : Configuration N) (j : ℕ) :
    gap X ((j % (N : ℕ) : ℕ) : ℤ) = gap X (j : ℤ) := by
  have hj : (j : ℤ) = (j % (N : ℕ) : ℕ) + (N : ℕ) * ((j / (N : ℕ) : ℕ) : ℤ) := by
    exact_mod_cast (Nat.mod_add_div j (N : ℕ)).symm
  conv_rhs => rw [hj]
  exact (rigidity_gap_add_mul X _ _).symm

theorem rigidityBlockSum_gapVector {N : ℕ+} (X : Configuration N)
    (i : Fin (N : ℕ)) (k : ℕ) :
    rigidityBlockSum N (gapVector X) i k = blockLength X (i : ℕ) k := by
  let : NeZero (N : ℕ) := ⟨N.ne_zero⟩
  rw [rigidityBlockSum, blockLength_eq_sum]
  apply sum_congr rfl
  intro r _
  change gap X ((i + (↑r : Fin (N : ℕ))).val : ℤ) = gap X ((i : ℕ) + r)
  rw [Fin.val_add, Fin.val_natCast, Nat.add_mod_mod]
  simpa only [Nat.cast_add] using rigidity_gap_nat_mod X (i.val + r)

theorem rigidityBlockSum_rotate (N : ℕ+) (y : Fin (N : ℕ) → ℝ)
    (i : Fin (N : ℕ)) (k : ℕ) :
    rigidityBlockSum N (fun r => y (finRotate (N : ℕ) r)) i k =
      rigidityBlockSum N y (finRotate (N : ℕ) i) k := by
  let : NeZero (N : ℕ) := ⟨N.ne_zero⟩
  apply sum_congr rfl
  intro r _
  simp only [finRotate_apply]
  congr 1
  abel

theorem measurable_rigidityBlockSum (N : ℕ+) (i : Fin (N : ℕ)) (k : ℕ) :
    Measurable (fun y => rigidityBlockSum N y i k) := by
  unfold rigidityBlockSum
  exact Finset.measurable_sum _ fun _ _ => measurable_pi_apply _

theorem rigidity_blockLength_boundaryLabel (N : ℕ+) (a : UnitAddCircle) (ell : ℝ)
    (X : Configuration N) (k : ℕ) :
    blockLength X ((boundaryCyclicLabel N a ell X : Fin (N : ℕ)) : ℕ) k =
      blockLength X (precedingLabel a ell X) k := by
  obtain ⟨q, hq⟩ := (boundaryCyclicLabel_eq_iff N a ell X _).mp rfl
  rw [hq]
  unfold blockLength
  rw [show ((boundaryCyclicLabel N a ell X : Fin (N : ℕ)) : ℤ) + (N : ℕ) * q + k =
      (((boundaryCyclicLabel N a ell X : Fin (N : ℕ)) : ℤ) + k) + (N : ℕ) * q by ring,
    boundary_cyclicLift_add_mul, boundary_cyclicLift_add_mul]
  ring

/-- The square-root cost of selecting a block at the boundary. -/
theorem rigidity_boundary_block_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ (_hPL : External.PrekopaLeindler) (P : Parameters)
      (N : ℕ+) (_hN : 2 ≤ (N : ℕ)) (a : UnitAddCircle) (ell : ℝ) (k : ℕ) (t : ℝ),
      (gibbsMeasure P N).real {X | t ≤ |blockLength X (precedingLabel a ell X) k - k|} ≤
        B * ((gibbsMeasure P N).real {X | t ≤ |blockLength X 0 k - k|}) ^ (1 / (2 : ℝ)) := by
  obtain ⟨B, hB, hb⟩ := boundary_selection_probability_bound
  refine ⟨B, hB, ?_⟩
  intro hPL P N hN a ell k t
  let A := fun i : Fin (N : ℕ) => {y | t ≤ |rigidityBlockSum N y i k - k|}
  have hA (i : Fin (N : ℕ)) : MeasurableSet (A i) :=
    measurableSet_le measurable_const (continuous_abs.measurable.comp ((measurable_rigidityBlockSum N i k).sub_const k))
  have hcyc : ∀ i y, y ∈ gapSimplex N →
      ((fun r => y (finRotate (N : ℕ) r)) ∈ A i ↔ y ∈ A (finRotate (N : ℕ) i)) := by
    intro i y _
    simp only [A, Set.mem_ofPred_eq, rigidityBlockSum_rotate]
  have he := hb hPL P N hN a ell A hA hcyc
  have hs : {X : Configuration N | gapVector X ∈ A (boundaryCyclicLabel N a ell X)} =
      {X | t ≤ |blockLength X (precedingLabel a ell X) k - k|} := by
    ext X
    simp only [A, Set.mem_ofPred_eq, rigidityBlockSum_gapVector,
      rigidity_blockLength_boundaryLabel]
  have hz : gapVector ⁻¹' A 0 = {X : Configuration N | t ≤ |blockLength X 0 k - k|} := by
    ext X
    simp only [A, Set.mem_preimage, Set.mem_ofPred_eq, rigidityBlockSum_gapVector,
      Fin.val_zero, Nat.cast_zero]
  rwa [hs, hz] at he

end Riesz1.Internal

end
