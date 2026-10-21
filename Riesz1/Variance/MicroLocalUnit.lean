/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.MicroLocalMoments

/-!
# Microscopic local second moment on the unit circle

Lemma 5.3, before rescaling arclength.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace Riesz1

theorem lintegral_rotation_mul_microLocalRow (P : Parameters) (N : ℕ+)
    (i : ℤ) (R : ℝ) (F : UnitAddCircle → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ X : Configuration N, F (cyclicLift X i) *
      ENNReal.ofReal (microLocalRow R X i) ∂gibbsMeasure P N) =
      (∫⁻ u, F u) * ∫⁻ X : Configuration N,
        ENNReal.ofReal (microLocalRow R X i) ∂gibbsMeasure P N := by
  have hI := (indepFun_cyclicLift_microLocalRow P N i i R).comp hF
    measurable_id.ennreal_ofReal
  have he := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
    (hF.comp (measurable_coe_circle.comp (measurable_cyclicLift i))).aemeasurable
    ((measurable_microLocalRow R i).ennreal_ofReal).aemeasurable hI
  simp only [Function.comp_apply] at he
  rw [he]
  congr 1
  exact (lintegral_map hF (measurable_coe_circle.comp (measurable_cyclicLift i))).symm.trans
    (congrArg (fun μ => ∫⁻ u, F u ∂μ) (map_cyclicLift_gibbsMeasure P N i))

/-- **Microscopic local second moment**, Lemma 5.3,
in unit-circle coordinates. The test need only be measurable: the extended
nonnegative inequality remains valid even when its right side is infinite. -/
theorem micro_local_unit (P : Parameters) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (N : ℕ+)
      (I : Set UnitAddCircle)
      (_hI : ∀ u ∈ I, ∀ v ∈ I, dist u v ≤ R / (N : ℝ))
      (f : UnitAddCircle → ℝ) (_hf : Measurable f) (_hsupp : ∀ u ∉ I, f u = 0),
      (∫⁻ X : Configuration N, ENNReal.ofReal ((∑ i : Fin (N : ℕ), |f (X.val i)|) ^ 2)
        ∂gibbsMeasure P N) ≤
          ENNReal.ofReal C * ENNReal.ofReal (N : ℝ) * ∫⁻ u, ENNReal.ofReal (f u ^ 2) := by
  obtain ⟨C, hC, hrow⟩ := microLocal_row_uniform P R
  refine ⟨C, hC, ?_⟩
  intro hPL N I hI f hf hsupp
  have hnonneg (X : Configuration N) (i : Fin (N : ℕ)) :
      0 ≤ f (X.val i) ^ 2 * microLocalRow R X (i : ℕ) :=
    mul_nonneg (sq_nonneg _) (microLocalRow_nonneg R X _)
  have hmeas (i : Fin (N : ℕ)) : Measurable (fun X : Configuration N =>
      ENNReal.ofReal (f (X.val i) ^ 2 * microLocalRow R X (i : ℕ))) :=
    (((hf.comp (measurable_coord N i)).pow_const 2).mul
      (measurable_microLocalRow R (i : ℕ))).ennreal_ofReal
  calc
    _ ≤ ∫⁻ X : Configuration N, ENNReal.ofReal
        (∑ i : Fin (N : ℕ), f (X.val i) ^ 2 * microLocalRow R X (i : ℕ)) ∂gibbsMeasure P N :=
      lintegral_mono fun X => ENNReal.ofReal_le_ofReal (microLocal_statistic_sq_le R X I hI f hsupp)
    _ = ∑ i : Fin (N : ℕ), ∫⁻ X : Configuration N,
        ENNReal.ofReal (f (X.val i) ^ 2 * microLocalRow R X (i : ℕ)) ∂gibbsMeasure P N := by
      simp_rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => hnonneg _ i)]
      exact lintegral_finsetSum _ (fun i _ => hmeas i)
    _ ≤ ∑ _i : Fin (N : ℕ), (∫⁻ u, ENNReal.ofReal (f u ^ 2)) * ENNReal.ofReal C := by
      apply sum_le_sum
      intro i _
      simp_rw [ENNReal.ofReal_mul (sq_nonneg _), ← cyclicLift_natCast _ i]
      rw [lintegral_rotation_mul_microLocalRow P N (i : ℕ) R _
        (hf.pow_const 2).ennreal_ofReal]
      exact mul_le_mul_of_nonneg_left (hrow hPL N (i : ℕ)).choose_spec zero_le
    _ = _ := by
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [ENNReal.ofReal_natCast]
      ring

end Riesz1

end
