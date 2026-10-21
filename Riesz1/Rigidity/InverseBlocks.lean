/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.NoExplosionUniform
public import Riesz1.Rigidity.NoExplosionBlocks

/-!
# Uniform inverse moments of blocks

This is part of Lemma 4.5, including every positive block length
and the one-particle convention. No independence of gaps is used.
-/

public section

noncomputable section

open MeasureTheory

namespace Riesz1

/-- **Inverse moments of longer blocks**, part of Lemma 4.5.
The same constant works for all positive lengths, hence for `1 ≤ L ≤ N`. -/
theorem inverse_blocks_uniform (P : Parameters) {p : ℝ} (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (N : ℕ+) (j : ℤ)
      (L : ℕ), 0 < L →
      ∃ _h : Integrable (fun X : Configuration N => blockLength X j L ^ (-p)) (gibbsMeasure P N),
        (∫⁻ X : Configuration N, ENNReal.ofReal (blockLength X j L ^ (-p)) ∂gibbsMeasure P N) ≤
          ENNReal.ofReal (C * (L : ℝ) ^ (-p)) := by
  obtain ⟨C, hC, hg⟩ := no_explosion_uniform P hp
  refine ⟨C, hC, ?_⟩
  intro hPL N j L hL
  let := (modelWellDefined P N).2.2
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hi (r : ℕ) := (hg hPL N (j + r)).choose
  have hb (r : ℕ) : (∫ X : Configuration N, gap X (j + r) ^ (-p) ∂gibbsMeasure P N) ≤ C := by
    have hh := (hg hPL N (j + r)).choose_spec
    rw [← ofReal_integral_eq_lintegral_ofReal (hi r)
      (ae_of_all _ fun X => Real.rpow_nonneg (gap_pos X _).le _)] at hh
    exact (ENNReal.ofReal_le_ofReal_iff hC.le).mp hh
  have his : Integrable (fun X : Configuration N => (L : ℝ) ^ (-p) * ((L : ℝ)⁻¹ *
      ∑ r ∈ Finset.range L, gap X (j + r) ^ (-p))) (gibbsMeasure P N) :=
    ((integrable_finsetSum _ (fun r _ => hi r)).const_mul _).const_mul _
  have hib : Integrable (fun X : Configuration N => blockLength X j L ^ (-p)) (gibbsMeasure P N) := by
    apply his.mono' ((measurable_blockLength j L).pow_const (-p)).aestronglyMeasurable
    exact ae_of_all _ fun X => by
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (blockLength_pos X j hL).le _)]
      exact blockLength_inverse_rpow_le X j hL hp
  refine ⟨hib, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hib
    (ae_of_all _ fun X => Real.rpow_nonneg (blockLength_pos X j hL).le _)]
  apply ENNReal.ofReal_le_ofReal
  calc (∫ X : Configuration N, blockLength X j L ^ (-p) ∂gibbsMeasure P N) ≤
        ∫ X : Configuration N, (L : ℝ) ^ (-p) * ((L : ℝ)⁻¹ *
          ∑ r ∈ Finset.range L, gap X (j + r) ^ (-p)) ∂gibbsMeasure P N :=
          integral_mono hib his (fun X => blockLength_inverse_rpow_le X j hL hp)
    _ = (L : ℝ) ^ (-p) * ((L : ℝ)⁻¹ *
        ∑ r ∈ Finset.range L, ∫ X : Configuration N, gap X (j + r) ^ (-p) ∂gibbsMeasure P N) := by
          rw [integral_const_mul, integral_const_mul, integral_finsetSum _ (fun r _ => hi r)]
    _ ≤ (L : ℝ) ^ (-p) * ((L : ℝ)⁻¹ * ∑ _r ∈ Finset.range L, C) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum (fun r _ => hb r)) (inv_nonneg.mpr hLr.le))
            (Real.rpow_nonneg hLr.le _)
    _ = C * (L : ℝ) ^ (-p) := by simp [hLr.ne']; ring

end Riesz1

end
