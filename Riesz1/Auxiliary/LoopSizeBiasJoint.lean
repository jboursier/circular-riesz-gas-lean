/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopSizeBiasRotation

/-!
# Selecting the preceding particle in rotation coordinates

The rotation window of any specified cyclic label is a condition on that particle's
rooted gap vector and displacement. Its unconditioned pair law is already a product.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Riesz1.Internal

/-- The region selecting the particle just before zero. -/
def loopSelectionWindow (N : ℕ+) : Set ((Fin (N : ℕ) → ℝ) × ℝ) :=
  {p | p.2 < p.1 ⟨0, N.pos⟩}

theorem measurableSet_loopSelectionWindow (N : ℕ+) : MeasurableSet (loopSelectionWindow N) :=
  measurableSet_lt measurable_snd ((measurable_pi_apply _).comp measurable_fst)

theorem loopParticlePair_mem_window (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (i : Fin (N : ℕ))
    (X : Configuration N) :
    loopParticlePair N i X ∈ loopSelectionWindow N ↔ boundaryCyclicLabel N 0 0 X = i := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hb : leftLift (0 : UnitAddCircle) 0 = 0 := by
    simp only [leftLift, AddCircle.coe_zero, sub_zero]
    change (AddCircle.equivIco (1 : ℝ) 0 (QuotientAddGroup.mk (0 : ℝ)) : ℝ) = 0
    rw [AddCircle.coe_equivIco_mk_apply]
    norm_num
  have hd : loopRotationDisplacement N (cyclicLift X (i : ℕ)) =
      (N : ℝ) * Int.fract (-cyclicLift X (i : ℕ)) := by
    unfold loopRotationDisplacement
    rw [show (0 : UnitAddCircle) - (cyclicLift X (i : ℕ) : UnitAddCircle) =
        ((-cyclicLift X (i : ℕ) : ℝ) : UnitAddCircle) by simp,
      AddCircle.coe_equivIco_mk_apply]
    simp only [div_one, mul_one]
  have hg : (shiftFin N (i : ℕ) (gapVector X)) ⟨0, N.pos⟩ = gap X (i : ℕ) := by
    unfold shiftFin
    rw [Fin.val_mk, Nat.cast_zero, add_zero, ← gap_eq_gapOf_gapVector]
  change loopRotationDisplacement N (cyclicLift X (i : ℕ)) <
    (shiftFin N (i : ℕ) (gapVector X)) ⟨0, N.pos⟩ ↔ _
  rw [hd, hg, boundaryCyclicLabel_eq_iff, precedingLabel_cyclic_iff_fract hN, hb, zero_sub]
  rw [lt_div_iff₀ hNr, mul_comm (Int.fract _) (N : ℝ)]

/-- The pair associated with the preceding cyclic label. -/
def loopBoundaryPair (N : ℕ+) (X : Configuration N) : (Fin (N : ℕ) → ℝ) × ℝ :=
  loopParticlePair N (boundaryCyclicLabel N 0 0 X) X

theorem measurable_loopBoundaryPair (N : ℕ+) : Measurable (loopBoundaryPair N) := by
  have hm : Measurable (fun p : Configuration N × Fin (N : ℕ) => loopParticlePair N p.2 p.1) :=
    measurable_from_prod_countable_left fun i => measurable_loopParticlePair N i
  exact hm.comp (measurable_id.prodMk (measurable_boundaryCyclicLabel N 0 0))

/-- The finite selection sum for the joint pair. Each summand is the same restricted product
law, because cyclic rerooting preserves the complete gap law. -/
theorem loopBoundaryPair_apply (P : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    {E : Set ((Fin (N : ℕ) → ℝ) × ℝ)} (hE : MeasurableSet E) :
    (gibbsMeasure P N).map (loopBoundaryPair N) E =
      (N : ℝ≥0∞) *
        (((gibbsMeasure P N).map gapVector).prod
          (ENNReal.ofReal ((N : ℝ)⁻¹) • volume.restrict (Ico (0 : ℝ) N)))
            (E ∩ loopSelectionWindow N) := by
  classical
  let A (i : Fin (N : ℕ)) : Set (Configuration N) :=
    {X | boundaryCyclicLabel N 0 0 X = i ∧ loopParticlePair N i X ∈ E}
  have hm (i : Fin (N : ℕ)) : MeasurableSet (A i) :=
    (measurableSet_eq_fun (measurable_boundaryCyclicLabel N 0 0) measurable_const).inter
      (measurable_loopParticlePair N i hE)
  have hd : Pairwise (fun i j => Disjoint (A i) (A j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro X hi hj
    exact hij (hi.1.symm.trans hj.1)
  have hu : loopBoundaryPair N ⁻¹' E = ⋃ i, A i := by
    ext X
    constructor
    · intro hx
      exact mem_iUnion.mpr ⟨boundaryCyclicLabel N 0 0 X, rfl, hx⟩
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      change loopParticlePair N (boundaryCyclicLabel N 0 0 X) X ∈ E
      rw [hi.1]
      exact hi.2
  rw [Measure.map_apply (measurable_loopBoundaryPair N) hE, hu, measure_iUnion hd hm, tsum_fintype]
  have he (i : Fin (N : ℕ)) : A i = loopParticlePair N i ⁻¹' (E ∩ loopSelectionWindow N) := by
    ext X
    exact and_comm.trans (and_congr_right fun _ => (loopParticlePair_mem_window N hN i X).symm)
  simp_rw [he, ← Measure.map_apply (measurable_loopParticlePair N _) (hE.inter
    (measurableSet_loopSelectionWindow N)), map_loopParticlePair P N hN]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The factor `N` from cyclic labels cancels the Jacobian `1/N`. -/
theorem map_loopBoundaryPair_clipped (P : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) :
    (gibbsMeasure P N).map (loopBoundaryPair N) =
      (((gibbsMeasure P N).map gapVector).prod (volume.restrict (Ico (0 : ℝ) N))).restrict
        (loopSelectionWindow N) := by
  have := (modelWellDefined P N).2.2
  have hNr : (0 : ℝ) < N := by exact_mod_cast N.pos
  ext E hE
  rw [loopBoundaryPair_apply P N hN hE, Measure.restrict_apply hE,
    Measure.prod_smul_right, Measure.smul_apply, smul_eq_mul, ← mul_assoc,
    ENNReal.ofReal_inv_of_pos hNr, ENNReal.ofReal_natCast,
    ENNReal.mul_inv_cancel (by exact_mod_cast N.ne_zero : ((N : ℕ) : ℝ≥0∞) ≠ 0)
      (ENNReal.natCast_ne_top _), one_mul]

/-- The true gap is less than the circumference, so the artificial full-displacement interval
can be removed. Its lower endpoint has zero Lebesgue measure. -/
theorem map_loopBoundaryPair (P : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) :
    (gibbsMeasure P N).map (loopBoundaryPair N) =
      (((gibbsMeasure P N).map gapVector).prod (volume : Measure ℝ)).restrict
        {p | 0 < p.2 ∧ p.2 < p.1 ⟨0, N.pos⟩} := by
  have := (modelWellDefined P N).2.2
  let ν := (gibbsMeasure P N).map gapVector
  have hg : ∀ᵐ g ∂ν, g ⟨0, N.pos⟩ < (N : ℝ) := by
    apply (ae_map_iff (measurable_gapVector _).aemeasurable
      (measurableSet_lt (measurable_pi_apply _) measurable_const)).mpr
    exact ae_of_all _ fun X => gap_lt_particle_number hN X 0
  have hp : ∀ᵐ p ∂ν.prod (volume : Measure ℝ), p.1 ⟨0, N.pos⟩ < (N : ℝ) ∧ p.2 ≠ 0 := by
    apply (Measure.ae_prod_iff_ae_ae ((measurableSet_lt ((measurable_pi_apply _).comp measurable_fst)
      measurable_const).inter (measurableSet_eq_fun measurable_snd measurable_const).compl)).mpr
    filter_upwards [hg] with g hg'
    filter_upwards [show ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 0 from by
      rw [ae_iff]
      simp only [not_not, Set.ofPred_eq_eq_singleton, measure_singleton]] with t ht
    exact ⟨hg', ht⟩
  rw [map_loopBoundaryPair_clipped P N hN]
  have he : ν.prod (volume.restrict (Ico (0 : ℝ) N)) =
      (ν.prod volume).restrict (univ ×ˢ Ico (0 : ℝ) N) := by
    simpa only [Measure.restrict_univ] using
      (Measure.prod_restrict (μ := ν) (ν := (volume : Measure ℝ)) (s := univ) (t := Ico (0 : ℝ) N))
  rw [he, Measure.restrict_restrict (measurableSet_loopSelectionWindow N)]
  apply Measure.restrict_congr_set
  filter_upwards [hp] with p hp'
  apply propext
  change (p.2 < p.1 ⟨0, N.pos⟩ ∧ (p.1 ∈ univ ∧ 0 ≤ p.2 ∧ p.2 < (N : ℝ))) ↔ _
  simp only [mem_univ, true_and]
  constructor
  · rintro ⟨h, h0, _⟩
    exact ⟨lt_of_le_of_ne h0 hp'.2.symm, h⟩
  · rintro ⟨h0, h⟩
    exact ⟨h, h0.le, h.trans hp'.1⟩

end Riesz1.Internal

end
