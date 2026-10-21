/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.BoundarySelectionLawLocal

/-!
# The finite size-bias identity at a boundary

The first equality in part of the proof of Theorem 1.
The event family may be arbitrary: cyclic equivariance is needed only for
the further reduction to the contribution of one label.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

/-- The preceding label reduced to the canonical finite cyclic label. -/
def boundaryCyclicLabel (N : ℕ+) (a : UnitAddCircle) (ℓ : ℝ) (X : Configuration N) : Fin (N : ℕ) :=
  ⟨(precedingLabel a ℓ X % (N : ℕ)).toNat, by
    have hp : (0 : ℤ) < (N : ℕ) := by exact_mod_cast N.pos
    have hn := Int.emod_nonneg (precedingLabel a ℓ X) hp.ne'
    have hh := Int.emod_lt_of_pos (precedingLabel a ℓ X) hp
    omega⟩

theorem measurable_boundaryCyclicLabel (N : ℕ+) (a : UnitAddCircle) (ℓ : ℝ) :
    Measurable (boundaryCyclicLabel N a ℓ) := by
  exact (Measurable.of_discrete (f := fun j : ℤ => (⟨(j % (N : ℕ)).toNat, by
    have hp : (0 : ℤ) < (N : ℕ) := by exact_mod_cast N.pos
    have hn := Int.emod_nonneg j hp.ne'
    have hh := Int.emod_lt_of_pos j hp
    omega⟩ : Fin (N : ℕ)))).comp (measurable_precedingLabel a ℓ)

theorem boundaryCyclicLabel_eq_iff (N : ℕ+) (a : UnitAddCircle) (ℓ : ℝ)
    (X : Configuration N) (i : Fin (N : ℕ)) :
    boundaryCyclicLabel N a ℓ X = i ↔
      ∃ q : ℤ, precedingLabel a ℓ X = (i : ℕ) + ((N : ℕ) : ℤ) * q := by
  have hp : (0 : ℤ) < (N : ℕ) := by exact_mod_cast N.pos
  constructor
  · intro h
    have hv := congrArg Fin.val h
    change (precedingLabel a ℓ X % (N : ℕ)).toNat = (i : ℕ) at hv
    refine ⟨precedingLabel a ℓ X / (N : ℕ), ?_⟩
    have hn := Int.emod_nonneg (precedingLabel a ℓ X) hp.ne'
    have he := Int.emod_add_mul_ediv (precedingLabel a ℓ X) (N : ℕ)
    omega
  · rintro ⟨q, hq⟩
    apply Fin.ext
    change (precedingLabel a ℓ X % (N : ℕ)).toNat = (i : ℕ)
    rw [hq, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast i.isLt),
      Int.toNat_natCast]

/-- The exact size-bias sum for any finite family of Borel gap events.
This is the first probability equality in part of the proof of Theorem 1.
The normalization is inside each nonnegative integral, so finiteness is never implicit. -/
theorem boundary_selection_sum (P : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (a : UnitAddCircle) (ℓ : ℝ) (A : Fin (N : ℕ) → Set (Fin (N : ℕ) → ℝ))
    (hA : ∀ i, MeasurableSet (A i)) :
    (gibbsMeasure P N) {X | gapVector X ∈ A (boundaryCyclicLabel N a ℓ X)} =
      ∑ i : Fin (N : ℕ), ∫⁻ X in gapVector ⁻¹' A i,
        ENNReal.ofReal (gap X (i : ℕ) / (N : ℝ)) ∂gibbsMeasure P N := by
  let E := fun i : Fin (N : ℕ) => {X : Configuration N |
    boundaryCyclicLabel N a ℓ X = i ∧ gapVector X ∈ A i}
  have hm (i : Fin (N : ℕ)) : MeasurableSet (E i) :=
    (measurableSet_eq_fun (measurable_boundaryCyclicLabel N a ℓ) measurable_const).inter
      (measurable_gapVector N (hA i))
  have hd : Pairwise (fun i j => Disjoint (E i) (E j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro X hXi hXj
    exact hij (hXi.1.symm.trans hXj.1)
  have he : {X : Configuration N | gapVector X ∈ A (boundaryCyclicLabel N a ℓ X)} = ⋃ i, E i := by
    ext X
    constructor
    · intro hX
      exact mem_iUnion.mpr ⟨boundaryCyclicLabel N a ℓ X, rfl, hX⟩
    · intro hX
      obtain ⟨i, hi⟩ := mem_iUnion.mp hX
      change gapVector X ∈ A (boundaryCyclicLabel N a ℓ X)
      rw [hi.1]
      exact hi.2
  rw [he, measure_iUnion hd hm, tsum_fintype]
  apply Finset.sum_congr rfl
  intro i _
  have hEi : E i = {X : Configuration N |
      (∃ q : ℤ, precedingLabel a ℓ X = (i : ℕ) + ((N : ℕ) : ℤ) * q) ∧ gapVector X ∈ A i} := by
    ext X
    exact and_congr (boundaryCyclicLabel_eq_iff N a ℓ X i) Iff.rfl
  rw [hEi]
  exact boundary_selection_one_label P N hN a ℓ i (A i) (hA i)

end Riesz1

end
