/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopSizeBiasWeight
public import Riesz1.CLT.SelectionCyclic

/-!
# Marginal law at the preceding-particle anchor

The boundary-selection sum is reduced by cyclic invariance of the entire gap vector.
This first gives the size-biased law in gap coordinates. Summing consecutive gaps then
recovers the preceding-particle anchored offsets.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Riesz1

namespace Internal

/-- The gap vector rerooted at the canonical preceding cyclic label. The formula has its
usual weak-boundary interpretation even at configurations with a particle at zero. -/
def loopBoundaryGaps (N : ℕ+) (X : Configuration N) : Fin (N : ℕ) → ℝ :=
  shiftFin N (boundaryCyclicLabel N 0 0 X : ℕ) (gapVector X)

theorem measurable_loopBoundaryGaps (N : ℕ+) : Measurable (loopBoundaryGaps N) := by
  apply Measurable.of_eval
  intro k
  have hm : Measurable (fun p : (Fin (N : ℕ) → ℝ) × Fin (N : ℕ) =>
      p.1 (modFin N ((p.2 : ℕ) + (k : ℕ)))) :=
    measurable_from_prod_countable_left fun i => by
      change Measurable (fun g : Fin (N : ℕ) → ℝ => g (modFin N ((i : ℕ) + (k : ℕ))))
      exact measurable_pi_apply _
  exact hm.comp ((measurable_gapVector N).prodMk (measurable_boundaryCyclicLabel N 0 0))

/-- The complete gap vector at the preceding particle has the gap-weighted base law. -/
theorem map_loopBoundaryGaps (P : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) :
    (gibbsMeasure P N).map (loopBoundaryGaps N) =
      ((gibbsMeasure P N).map gapVector).withDensity (fun g => ENNReal.ofReal (g ⟨0, N.pos⟩)) := by
  classical
  ext E hE
  let A : Fin (N : ℕ) → Set (Fin (N : ℕ) → ℝ) := fun i => shiftFin N (i : ℕ) ⁻¹' E
  have hA (i : Fin (N : ℕ)) : MeasurableSet (A i) := measurable_shiftFin _ hE
  rw [Measure.map_apply (measurable_loopBoundaryGaps N) hE,
    withDensity_apply _ hE]
  change (gibbsMeasure P N) {X | gapVector X ∈ A (boundaryCyclicLabel N 0 0 X)} = _
  rw [boundary_selection_sum P N hN 0 0 A hA]
  let K : (Fin (N : ℕ) → ℝ) → ℝ≥0∞ :=
    E.indicator (fun g => ENNReal.ofReal (g ⟨0, N.pos⟩ / (N : ℝ)))
  have hK : Measurable K := ((measurable_pi_apply _).div_const _).ennreal_ofReal.indicator hE
  have he (i : Fin (N : ℕ)) :
      (∫⁻ X in gapVector ⁻¹' A i, ENNReal.ofReal (gap X (i : ℕ) / (N : ℝ)) ∂gibbsMeasure P N) =
        ∫⁻ X, K (gapVector X) ∂gibbsMeasure P N := by
    rw [← lintegral_shiftFin_gapVector P hN K hK i.val,
      ← lintegral_indicator (measurable_gapVector N (hA i))]
    apply lintegral_congr
    intro X
    by_cases hX : gapVector X ∈ A i
    · rw [Set.indicator_of_mem (show X ∈ gapVector ⁻¹' A i from hX)]
      change _ = E.indicator _ (shiftFin N (i : ℕ) (gapVector X))
      rw [Set.indicator_of_mem (show shiftFin N (i : ℕ) (gapVector X) ∈ E from hX)]
      unfold shiftFin
      simp only [Nat.cast_zero, add_zero, ← gap_eq_gapOf_gapVector]
    · rw [Set.indicator_of_notMem (show X ∉ gapVector ⁻¹' A i from hX)]
      exact (Set.indicator_of_notMem (show shiftFin N (i : ℕ) (gapVector X) ∉ E from hX) _).symm
  simp_rw [he]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hNr : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hKI : (∫⁻ X, K (gapVector X) ∂gibbsMeasure P N) =
      ENNReal.ofReal ((N : ℝ)⁻¹) *
        ∫⁻ g in E, ENNReal.ofReal (g ⟨0, N.pos⟩) ∂(gibbsMeasure P N).map gapVector := by
    rw [← lintegral_map hK (measurable_gapVector N)]
    dsimp only [K]
    rw [lintegral_indicator hE]
    simp_rw [div_eq_inv_mul, ENNReal.ofReal_mul (inv_nonneg.mpr hNr.le)]
    rw [lintegral_const_mul _ (measurable_pi_apply _).ennreal_ofReal]
  rw [hKI, ← mul_assoc, ENNReal.ofReal_inv_of_pos hNr, ENNReal.ofReal_natCast,
    ENNReal.mul_inv_cancel (by exact_mod_cast N.ne_zero : ((N : ℕ) : ℝ≥0∞) ≠ 0)
      (ENNReal.natCast_ne_top _), one_mul]

end Internal

end Riesz1

end
