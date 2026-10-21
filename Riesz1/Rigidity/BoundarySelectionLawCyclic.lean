/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.BoundarySelectionLaw
public import Riesz1.Rigidity.GapLawDensity

/-!
# Cyclic reduction of the size-bias sum

An arbitrary Borel cyclic family has the boundary-selected probability
equal to the gap-weighted probability at label zero.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Riesz1

/-- Every actual gap vector belongs to the positive simplex. -/
theorem boundary_gapVector_mem_simplex {N : ℕ+} (X : Configuration N) : gapVector X ∈ gapSimplex N := by
  refine ⟨fun i => gap_pos X (i : ℕ), ?_⟩
  change (∑ i : Fin (N : ℕ), gap X (i : ℕ)) = (N : ℝ)
  exact (Fin.sum_univ_eq_sum_range (fun k : ℕ => gap X (k : ℤ)) (N : ℕ)).trans (sum_gap_eq X)

/-- An invariant function on a finite cycle is constant. -/
theorem boundary_cycle_invariant_eq {n : ℕ} [NeZero n] {α : Type*}
    (f : Fin n → α) (hf : ∀ i, f (finRotate n i) = f i) (i : Fin n) : f i = f 0 := by
  have hi (k : ℕ) (j : Fin n) : f ((finRotate n)^[k] j) = f j := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', hf, ih]
  have he : (finRotate n)^[i.val] (0 : Fin n) = i := by
    rw [← finCycle_eq_finRotate_iterate]
    simp only [finCycle_apply, zero_add]
  rw [← he]
  exact hi i.val 0

/-- Cyclic equivariance of the event family and the actual gap law identify all
gap-weighted contributions. The hypothesis is the pointwise equivariance of events. -/
theorem cyclic_gap_event_weight_eq (P : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (A : Fin (N : ℕ) → Set (Fin (N : ℕ) → ℝ)) (hA : ∀ i, MeasurableSet (A i))
    (hcyc : ∀ i y, y ∈ gapSimplex N → ((fun r => y (finRotate (N : ℕ) r)) ∈ A i ↔ y ∈ A (finRotate (N : ℕ) i)))
    (i : Fin (N : ℕ)) :
    (∫⁻ X in gapVector ⁻¹' A i, ENNReal.ofReal (gap X (i : ℕ)) ∂gibbsMeasure P N) =
      ∫⁻ X in gapVector ⁻¹' A 0, ENNReal.ofReal (gap X 0) ∂gibbsMeasure P N := by
  let : NeZero (N : ℕ) := ⟨N.ne_zero⟩
  let F := fun (i : Fin (N : ℕ)) (y : Fin (N : ℕ) → ℝ) =>
    (A i).indicator (fun y => ENNReal.ofReal (y i)) y
  have hF (i : Fin (N : ℕ)) : Measurable (F i) :=
    (measurable_pi_apply i).ennreal_ofReal.indicator (hA i)
  have he (i : Fin (N : ℕ)) (y : Fin (N : ℕ) → ℝ) (hyS : y ∈ gapSimplex N) :
      F i (fun r => y (finRotate (N : ℕ) r)) = F (finRotate (N : ℕ) i) y := by
    dsimp only [F]
    by_cases hy : y ∈ A (finRotate (N : ℕ) i)
    · rw [Set.indicator_of_mem ((hcyc i y hyS).mpr hy), Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem (fun h => hy ((hcyc i y hyS).mp h)), Set.indicator_of_notMem hy]
  have hJ (i : Fin (N : ℕ)) :
      (∫⁻ X, F (finRotate (N : ℕ) i) (gapVector X) ∂gibbsMeasure P N) =
        ∫⁻ X, F i (gapVector X) ∂gibbsMeasure P N := by
    have hex (X : Configuration N) : F (finRotate (N : ℕ) i) (gapVector X) =
        F i (fun r => gapVector X (finRotate (N : ℕ) r)) :=
      (he i (gapVector X) (boundary_gapVector_mem_simplex X)).symm
    simp_rw [hex]
    have hT : Measurable (fun X : Configuration N => fun r => gapVector X (finRotate (N : ℕ) r)) :=
      Measurable.of_eval (fun r => (measurable_pi_apply (finRotate (N : ℕ) r)).comp (measurable_gapVector N))
    rw [← lintegral_map (hF i) hT,
      map_gapVector_cycle_gibbsMeasure P N hN, lintegral_map (hF i) (measurable_gapVector N)]
  have hh := boundary_cycle_invariant_eq
    (fun i => ∫⁻ X, F i (gapVector X) ∂gibbsMeasure P N) hJ i
  simpa only [F, ← Set.indicator_comp_right, lintegral_indicator (measurable_gapVector N (hA _)),
    Function.comp_def, gapVector, Fin.val_zero, Nat.cast_zero] using hh

/-- The size-biased probability identity for every cyclic Borel gap-event family,
the two equalities of the boundary part of Theorem 1. -/
theorem boundary_selection_size_bias (P : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (a : UnitAddCircle) (ℓ : ℝ) (A : Fin (N : ℕ) → Set (Fin (N : ℕ) → ℝ))
    (hA : ∀ i, MeasurableSet (A i))
    (hcyc : ∀ i y, y ∈ gapSimplex N → ((fun r => y (finRotate (N : ℕ) r)) ∈ A i ↔ y ∈ A (finRotate (N : ℕ) i))) :
    (gibbsMeasure P N) {X | gapVector X ∈ A (boundaryCyclicLabel N a ℓ X)} =
      ∫⁻ X in gapVector ⁻¹' A 0, ENNReal.ofReal (gap X 0) ∂gibbsMeasure P N := by
  let : NeZero (N : ℕ) := ⟨N.ne_zero⟩
  have hNr : (0 : ℝ) < (N : ℕ) := by exact_mod_cast N.pos
  rw [boundary_selection_sum P N hN a ℓ A hA]
  have he (i : Fin (N : ℕ)) :
      (∫⁻ X in gapVector ⁻¹' A i, ENNReal.ofReal (gap X (i : ℕ) / (N : ℝ)) ∂gibbsMeasure P N) =
        ENNReal.ofReal ((N : ℝ)⁻¹) *
          ∫⁻ X in gapVector ⁻¹' A 0, ENNReal.ofReal (gap X 0) ∂gibbsMeasure P N := by
    simp_rw [div_eq_inv_mul, ENNReal.ofReal_mul (inv_nonneg.mpr hNr.le)]
    rw [lintegral_const_mul _ ((measurable_gap _).ennreal_ofReal),
      cyclic_gap_event_weight_eq P N hN A hA hcyc i]
  simp_rw [he]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc]
  have hc : ((N : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((N : ℝ)⁻¹) = 1 := by
    rw [ENNReal.ofReal_inv_of_pos hNr, ENNReal.ofReal_natCast,
      ENNReal.mul_inv_cancel (by exact_mod_cast N.ne_zero : ((N : ℕ) : ENNReal) ≠ 0) (ENNReal.natCast_ne_top (N : ℕ))]
  rw [hc, one_mul]

end Riesz1

end
