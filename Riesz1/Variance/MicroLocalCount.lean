/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.MicroLocalGeometry

/-!
# Counting particles near a marked particle

The deterministic Cauchy--Schwarz step of Lemma 5.3.
-/

@[expose] public section

noncomputable section

open MeasureTheory Finset
open scoped ENNReal

namespace Riesz1

attribute [local instance] Classical.propDecidable

lemma microLocal_block_nonneg {N : ℕ+} (X : Configuration N) (i : ℤ) (L : ℕ) :
    0 ≤ blockLength X i L := by
  unfold blockLength
  exact mul_nonneg (by positivity) (sub_nonneg.mpr
    ((cyclicLift_strictMono X).monotone (by omega)))

/-- The inverse-block bound on the count seen from label `i`. -/
def microLocalRow {N : ℕ+} (R : ℝ) (X : Configuration N) (i : ℤ) : ℝ :=
  1 + R ^ 2 * ∑ r ∈ range ((N : ℕ) - 1),
    (blockLength X i (r + 1) ^ (-(2 : ℝ)) +
      blockLength X (i + (r + 1 : ℕ)) ((N : ℕ) - (r + 1)) ^ (-(2 : ℝ)))

theorem measurable_microLocalRow {N : ℕ+} (R : ℝ) (i : ℤ) :
    Measurable (fun X : Configuration N => microLocalRow R X i) := by
  unfold microLocalRow
  exact measurable_const.add (measurable_const.mul (Finset.measurable_sum _ fun r _ =>
    ((measurable_blockLength _ _).pow_const _).add
      ((measurable_blockLength _ _).pow_const _)))

theorem microLocalRow_nonneg {N : ℕ+} (R : ℝ) (X : Configuration N) (i : ℤ) :
    0 ≤ microLocalRow R X i := by
  unfold microLocalRow
  exact add_nonneg zero_le_one (mul_nonneg (sq_nonneg R) (sum_nonneg fun r _ =>
    add_nonneg (Real.rpow_nonneg (microLocal_block_nonneg X _ _) _)
      (Real.rpow_nonneg (microLocal_block_nonneg X _ _) _)))

/-- An arc may be replaced by any set with the same diameter bound. -/
theorem microLocal_count_le_row {N : ℕ+} (R : ℝ) (X : Configuration N)
    (I : Set UnitAddCircle)
    (hI : ∀ u ∈ I, ∀ v ∈ I, dist u v ≤ R / (N : ℝ))
    (i : ℤ) (hi : (cyclicLift X i : UnitAddCircle) ∈ I) :
    (∑ j : Fin (N : ℕ), if (X.val j : UnitAddCircle) ∈ I then (1 : ℝ) else 0) ≤
      microLocalRow R X i := by
  let G : ℤ → ℝ := fun j => if (cyclicLift X j : UnitAddCircle) ∈ I then 1 else 0
  have hper : ∀ j, G (j + (N : ℕ)) = G j := by
    intro j
    simp only [G, cyclicLift_add_N, AddCircle.coe_add_period]
  have he : (∑ j : Fin (N : ℕ), if (X.val j : UnitAddCircle) ∈ I then (1 : ℝ) else 0) =
      ∑ r ∈ range (N : ℕ), G (i + r) := by
    rw [sum_range_shift G hper i, ← Fin.sum_univ_eq_sum_range]
    exact sum_congr rfl fun j _ => by simp only [G, cyclicLift_natCast]
  have hN : (N : ℕ) = ((N : ℕ) - 1) + 1 := by have := N.pos; omega
  rw [he]
  rw [show range (N : ℕ) = range (((N : ℕ) - 1) + 1) by rw [← hN], sum_range_succ']
  simp only [Nat.cast_zero, add_zero, G, hi, ↓reduceIte]
  unfold microLocalRow
  rw [add_comm _ (1 : ℝ), mul_sum]
  apply add_le_add le_rfl
  apply sum_le_sum
  intro r hr
  have hkN : r + 1 < (N : ℕ) := by have := mem_range.mp hr; omega
  calc
    (if (cyclicLift X (i + (r + 1 : ℕ)) : UnitAddCircle) ∈ I then (1 : ℝ) else 0) ≤
        if dist (cyclicLift X i : UnitAddCircle)
          (cyclicLift X (i + (r + 1 : ℕ)) : UnitAddCircle) ≤ R / (N : ℝ) then 1 else 0 := by
            split_ifs with hm hd hd
            · rfl
            · exact False.elim (hd (hI _ hi _ hm))
            · norm_num
            · rfl
    _ ≤ _ := microLocal_pair_indicator X i (Nat.succ_pos r) hkN

/-- Configurationwise Cauchy--Schwarz with the local inverse-block weight. -/
theorem microLocal_statistic_sq_le {N : ℕ+} (R : ℝ) (X : Configuration N)
    (I : Set UnitAddCircle)
    (hI : ∀ u ∈ I, ∀ v ∈ I, dist u v ≤ R / (N : ℝ))
    (f : UnitAddCircle → ℝ) (hsupp : ∀ u ∉ I, f u = 0) :
    (∑ i : Fin (N : ℕ), |f (X.val i)|) ^ 2 ≤
      ∑ i : Fin (N : ℕ), f (X.val i) ^ 2 * microLocalRow R X (i : ℕ) := by
  let T := univ.filter (fun i : Fin (N : ℕ) => (X.val i : UnitAddCircle) ∈ I)
  have he : ∑ i : Fin (N : ℕ), |f (X.val i)| = ∑ i ∈ T, |f (X.val i)| := by
    symm
    apply sum_subset (filter_subset _ _)
    intro i _ hi
    simp only [mem_filter, mem_univ, true_and] at hi
    rw [hsupp _ hi, abs_zero]
  have hc : (T.card : ℝ) =
      ∑ j : Fin (N : ℕ), if (X.val j : UnitAddCircle) ∈ I then (1 : ℝ) else 0 := by
    simp [T, sum_boole]
  rw [he]
  calc
    (∑ i ∈ T, |f (X.val i)|) ^ 2 ≤ (T.card : ℝ) * ∑ i ∈ T, |f (X.val i)| ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    _ = ∑ i ∈ T, f (X.val i) ^ 2 * (T.card : ℝ) := by
      simp only [sq_abs, mul_sum]
      apply sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ i ∈ T, f (X.val i) ^ 2 * microLocalRow R X (i : ℕ) := by
      apply sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      rw [hc]
      apply microLocal_count_le_row R X I hI (i : ℕ)
      rw [cyclicLift_natCast]
      exact (mem_filter.mp hi).2
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun i _ _ => mul_nonneg (sq_nonneg _) (microLocalRow_nonneg R X _))

end Riesz1

end
