/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopSizeBiasJoint
public import Riesz1.Auxiliary.LoopSizeBiasBounds

/-!
# The preceding-particle joint law

The size-bias part of Lemma 5.8: the law of `(y,D)` is the product of anchored
probability and displacement Lebesgue measure, restricted to `0 < D < w(y)`.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Riesz1

private theorem boundaryPair_displacement {N : ℕ+} (X : LoopPrecedingConfiguration N) :
    (Internal.loopBoundaryPair N X.val).2 = loopPrecedingD X := by
  let j := loopPrecedingLabel X
  have hs := loopPrecedingLabel_spec X
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hbound : -1 < cyclicLift X.val j := by
    have hle := (cyclicLift_strictMono X.val).monotone
      (show j + 1 ≤ j + (N : ℕ) by have := N.pos; omega)
    rw [cyclicLift_add_N] at hle
    linarith [hs.2]
  have hrep : (AddCircle.equivIco (1 : ℝ) 0
      (0 - (cyclicLift X.val j : UnitAddCircle)) : ℝ) = -cyclicLift X.val j := by
    rw [show (0 : UnitAddCircle) - (cyclicLift X.val j : UnitAddCircle) =
      ((-cyclicLift X.val j : ℝ) : UnitAddCircle) by simp]
    exact AddCircle.equivIco_coe_of_mem ⟨by linarith [hs.1], by linarith⟩
  obtain ⟨q, hq⟩ := (boundaryCyclicLabel_eq_iff N 0 0 X.val (boundaryCyclicLabel N 0 0 X.val)).mp rfl
  have hc : (cyclicLift X.val (boundaryCyclicLabel N 0 0 X.val : ℕ) : UnitAddCircle) =
      (cyclicLift X.val j : UnitAddCircle) := by
    change _ = (cyclicLift X.val (precedingLabel 0 0 X.val) : UnitAddCircle)
    rw [hq, boundary_cyclicLift_add_mul, AddCircle.coe_add]
    simp
  change (N : ℝ) * (AddCircle.equivIco (1 : ℝ) 0
    (0 - (cyclicLift X.val (boundaryCyclicLabel N 0 0 X.val : ℕ) : UnitAddCircle)) : ℝ) = _
  rw [hc, hrep]
  change (N : ℝ) * -cyclicLift X.val j = -(N : ℝ) * cyclicLift X.val j
  ring

private theorem map_gapPair_offsets (P : Parameters) (n : ℕ) :
    ((((gibbsMeasure P (n + 1).succPNat).map gapVector).prod (volume : Measure ℝ)).restrict
      {p | 0 < p.2 ∧ p.2 < p.1 ⟨0, (n + 1).succPNat.pos⟩}).map
        (fun p => ((loopGapOffsets (n + 1).succPNat p.1 : Fin (n + 1) → ℝ), p.2)) =
      ((anchoredLaw P (n + 1)).prod (volume : Measure ℝ)).restrict
        {p | 0 < p.2 ∧ p.2 < loopSizeWeight n p.1} := by
  have := (modelWellDefined P (n + 1).succPNat).2.2
  let ν := (gibbsMeasure P (n + 1).succPNat).map gapVector
  let F : ((Fin (((n + 1).succPNat : ℕ)) → ℝ) × ℝ) → ((Fin (n + 1) → ℝ) × ℝ) :=
    fun p => (loopGapOffsets (n + 1).succPNat p.1, p.2)
  let T : Set ((Fin (n + 1) → ℝ) × ℝ) := {p | 0 < p.2 ∧ p.2 < loopSizeWeight n p.1}
  have hF : Measurable F :=
    ((measurable_loopGapOffsets _).comp measurable_fst).prodMk measurable_snd
  have hT : MeasurableSet T := (measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_lt measurable_snd ((measurable_loopSizeWeight n).comp measurable_fst))
  have hmap : (ν.prod (volume : Measure ℝ)).map F = (anchoredLaw P (n + 1)).prod volume := by
    have he := Measure.map_prod_map ν (volume : Measure ℝ)
      (f := fun g => (loopGapOffsets (n + 1).succPNat g : Fin (n + 1) → ℝ))
      (g := id) (measurable_loopGapOffsets _) measurable_id
    rw [Measure.map_id] at he
    exact he.symm.trans (congrArg (fun μ : Measure (Fin (n + 1) → ℝ) => μ.prod (volume : Measure ℝ))
      (map_loopGapOffsets P n))
  have hw : ∀ᵐ g ∂ν, g ⟨0, (n + 1).succPNat.pos⟩ = loopSizeWeight n (loopGapOffsets (n + 1).succPNat g) := by
    apply (ae_map_iff (measurable_gapVector _).aemeasurable
      (measurableSet_eq_fun (measurable_pi_apply _)
        ((measurable_loopSizeWeight n).comp (measurable_loopGapOffsets _)))).mpr
    exact ae_of_all _ fun X => by
      exact (loopSizeWeight_anchorCoords n X).symm.trans
        (congrArg (loopSizeWeight n) (loopGapOffsets_gapVector n X)).symm
  have hs : {p | 0 < p.2 ∧ p.2 < p.1 ⟨0, (n + 1).succPNat.pos⟩} =ᵐ[
      ν.prod (volume : Measure ℝ)] F ⁻¹' T := by
    have hh : ∀ᵐ p ∂ν.prod (volume : Measure ℝ), p.1 ⟨0, (n + 1).succPNat.pos⟩ =
        loopSizeWeight n (loopGapOffsets (n + 1).succPNat p.1) := by
      apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
        ((measurable_pi_apply _).comp measurable_fst)
        (((measurable_loopSizeWeight n).comp (measurable_loopGapOffsets _)).comp measurable_fst))).mpr
      exact hw.mono fun g hg => ae_of_all _ fun _ => hg
    filter_upwards [hh] with p hp
    apply propext
    change (0 < p.2 ∧ p.2 < p.1 ⟨0, (n + 1).succPNat.pos⟩) ↔
      (0 < p.2 ∧ p.2 < loopSizeWeight n (loopGapOffsets (n + 1).succPNat p.1))
    rw [hp]
  rw [Measure.restrict_congr_set hs]
  exact (Measure.restrict_map hF hT).symm.trans (congrArg (fun μ => μ.restrict T) hmap)

/-- The size-bias part of Lemma 5.8, the full joint-law formula, on exactly the
carrier of the preceding-particle variables. -/
theorem map_loopPrecedingJoint (P : Parameters) (n : ℕ) :
    (loopPrecedingMeasure P (n + 1).succPNat).map
      (fun X => (loopPrecedingOffsets X, loopPrecedingD X)) =
      ((anchoredLaw P (n + 1)).prod (volume : Measure ℝ)).restrict
        {p | 0 < p.2 ∧ p.2 < loopSizeWeight n p.1} := by
  let F : ((Fin (((n + 1).succPNat : ℕ)) → ℝ) × ℝ) → ((Fin (n + 1) → ℝ) × ℝ) :=
    fun p => (loopGapOffsets (n + 1).succPNat p.1, p.2)
  have hF : Measurable F :=
    ((measurable_loopGapOffsets _).comp measurable_fst).prodMk measurable_snd
  have hB := Internal.measurable_loopBoundaryPair (n + 1).succPNat
  have he (X : LoopPrecedingConfiguration (n + 1).succPNat) :
      F (Internal.loopBoundaryPair _ X.val) = (loopPrecedingOffsets X, loopPrecedingD X) :=
    Prod.ext (loopGapOffsets_preceding X) (boundaryPair_displacement X)
  calc
    _ = (((loopPrecedingMeasure P (n + 1).succPNat).map Subtype.val).map
        (Internal.loopBoundaryPair _)).map F := by
      rw [Measure.map_map hB measurable_subtype_coe,
        Measure.map_map hF (hB.comp measurable_subtype_coe)]
      congr 1
      funext X
      exact (he X).symm
    _ = _ := by
      rw [map_loopPrecedingMeasure, Internal.map_loopBoundaryPair P _ (by simp)]
      exact map_gapPair_offsets P n

end Riesz1

end
