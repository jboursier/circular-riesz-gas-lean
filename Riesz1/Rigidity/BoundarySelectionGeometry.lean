/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.GapLaw

/-!
# Measurability and geometry of boundary selection

Deterministic inputs to part of the proof of Theorem 1.
The probability identity for the size-biased selected gap is a separate step.
-/

public section

open MeasureTheory Set

namespace Riesz1

/-- Selecting a gap at the preceding label is measurable. -/
theorem measurable_gap_precedingLabel (N : ℕ+) (a : UnitAddCircle) (ℓ : ℝ) :
    Measurable (fun X : Configuration N => gap X (precedingLabel a ℓ X)) := by
  have hm : Measurable (fun p : Configuration N × ℤ => gap p.1 p.2) :=
    measurable_from_prod_countable_left fun j => measurable_gap j
  exact hm.comp (measurable_id.prodMk (measurable_precedingLabel a ℓ))

/-- Every countable family of Borel gap events gives a Borel selected event.
No cyclic-equivariance hypothesis is needed for measurability. -/
theorem measurableSet_selected_gap_event (N : ℕ+) (a : UnitAddCircle) (ℓ : ℝ)
    (A : ℤ → Set (Fin (N : ℕ) → ℝ)) (hA : ∀ j, MeasurableSet (A j)) :
    MeasurableSet {X : Configuration N | gapVector X ∈ A (precedingLabel a ℓ X)} := by
  have he : {X : Configuration N | gapVector X ∈ A (precedingLabel a ℓ X)} =
      ⋃ j : ℤ, {X | precedingLabel a ℓ X = j} ∩ gapVector ⁻¹' A j := by
    ext X
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_preimage]
    constructor
    · intro h
      exact ⟨precedingLabel a ℓ X, rfl, h⟩
    · rintro ⟨j, hj, h⟩
      rwa [hj]
  rw [he]
  exact MeasurableSet.iUnion fun j =>
    (measurableSet_eq_fun (measurable_precedingLabel a ℓ) measurable_const).inter
      (measurable_gapVector N (hA j))

/-- The microscopic distance from the preceding particle to the boundary lies
between zero and the selected gap. Endpoint equality on the left is allowed. -/
theorem boundary_displacement_mem (N : ℕ+) (a : UnitAddCircle) (ℓ : ℝ)
    (X : Configuration N) :
    0 ≤ (N : ℝ) * (leftLift a ℓ - cyclicLift X (precedingLabel a ℓ X)) ∧
      (N : ℝ) * (leftLift a ℓ - cyclicLift X (precedingLabel a ℓ X)) <
        gap X (precedingLabel a ℓ X) := by
  have hb := leftLift_mem a ℓ
  have hJ := preceding_spec X hb.1 hb.2
  have hN : (0 : ℝ) < (N : ℕ) := by exact_mod_cast N.pos
  constructor
  · exact mul_nonneg hN.le (sub_nonneg.mpr hJ.1)
  · unfold gap
    exact mul_lt_mul_of_pos_left (sub_lt_sub_right hJ.2 _) hN

end Riesz1

end
