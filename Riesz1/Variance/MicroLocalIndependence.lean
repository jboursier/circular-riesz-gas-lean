/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.InverseBlocks
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Analysis.PSeries

/-!
# Rotation and inverse block moments

The product-law step in the proof of Lemma 5.3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Riesz1

/-- Joint independence with the entire anchored configuration. -/
theorem indepFun_cyclicLift_anchorCoords (P : Parameters) (n : ℕ) (i : ℤ) :
    IndepFun (fun X : Configuration n.succPNat => (cyclicLift X i : UnitAddCircle))
      (fun X => (anchorCoords n X.val).2) (gibbsMeasure P n.succPNat) := by
  let := (modelWellDefined P n.succPNat).2.2
  have hA : Measurable (fun X : Configuration n.succPNat => (anchorCoords n X.val).2) :=
    measurable_snd.comp (measurable_anchorCoords_config n)
  have hrot : Measurable (fun X : Configuration n.succPNat =>
      (cyclicLift X i : UnitAddCircle)) :=
    measurable_coe_circle.comp (measurable_cyclicLift i)
  rw [indepFun_iff_map_prod_eq_prod_map_map hrot.aemeasurable hA.aemeasurable,
    map_cyclicLift_anchorCoords_gibbsMeasure, map_cyclicLift_gibbsMeasure]
  congr 1
  exact (map_snd_gibbsMeasure P n).symm

/-- A particle rotation is independent of every block length. -/
theorem indepFun_cyclicLift_blockLength (P : Parameters) (N : ℕ+) (i j : ℤ) (L : ℕ) :
    IndepFun (fun X : Configuration N => (cyclicLift X i : UnitAddCircle))
      (fun X => blockLength X j L) (gibbsMeasure P N) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = n.succPNat :=
    ⟨N.natPred, (PNat.succPNat_natPred N).symm⟩
  let A := fun X : Configuration n.succPNat => (anchorCoords n X.val).2
  have hI : IndepFun (fun X : Configuration n.succPNat =>
      (cyclicLift X i : UnitAddCircle)) A (gibbsMeasure P n.succPNat) :=
    indepFun_cyclicLift_anchorCoords P n i
  let B := fun y : Fin n → ℝ => (n.succPNat : ℝ) *
    (anchoredCyclicOffset n y (j + L) - anchoredCyclicOffset n y j)
  have hB : Measurable B := measurable_const.mul
    ((measurable_anchoredCyclicOffset n _).sub (measurable_anchoredCyclicOffset n _))
  have h := hI.comp measurable_id hB
  have he : (fun X : Configuration n.succPNat => blockLength X j L) = B ∘ A := by
    funext X
    simp only [Function.comp_apply, B, A, blockLength, cyclicLift_eq_anchor_add]
    ring
  rw [he]
  exact h

/-- The nonnegative weighted inverse-block integral factors without any integrability
assumption on the measurable test. This is the conditioning step of
Lemma 5.3. -/
theorem lintegral_rotation_mul_inverse_block (P : Parameters) (N : ℕ+)
    (i j : ℤ) (L : ℕ) (F : UnitAddCircle → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ X : Configuration N, F (cyclicLift X i) *
      ENNReal.ofReal (blockLength X j L ^ (-(2 : ℝ))) ∂gibbsMeasure P N) =
      (∫⁻ u, F u) * ∫⁻ X : Configuration N,
        ENNReal.ofReal (blockLength X j L ^ (-(2 : ℝ))) ∂gibbsMeasure P N := by
  have hI := (indepFun_cyclicLift_blockLength P N i j L).comp hF
    ((measurable_id.pow_const (-(2 : ℝ))).ennreal_ofReal)
  have he := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
    (hF.comp (measurable_coe_circle.comp (measurable_cyclicLift i))).aemeasurable
    (((measurable_blockLength j L).pow_const _).ennreal_ofReal).aemeasurable hI
  simp only [Function.comp_apply] at he
  rw [he]
  congr 1
  exact (lintegral_map hF (measurable_coe_circle.comp (measurable_cyclicLift i))).symm.trans
    (congrArg (fun μ => ∫⁻ u, F u ∂μ) (map_cyclicLift_gibbsMeasure P N i))

end Riesz1

end
