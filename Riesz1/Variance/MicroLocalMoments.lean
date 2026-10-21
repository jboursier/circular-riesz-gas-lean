/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.MicroLocalCount

/-!
# Uniform moments of the local count bound

The summable inverse-square estimate in Lemma 5.3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace Riesz1

theorem indepFun_cyclicLift_microLocalRow (P : Parameters) (N : ℕ+)
    (i j : ℤ) (R : ℝ) :
    IndepFun (fun X : Configuration N => (cyclicLift X i : UnitAddCircle))
      (fun X => microLocalRow R X j) (gibbsMeasure P N) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = n.succPNat :=
    ⟨N.natPred, (PNat.succPNat_natPred N).symm⟩
  let b := fun (y : Fin n → ℝ) (a : ℤ) (L : ℕ) => (n.succPNat : ℝ) *
    (anchoredCyclicOffset n y (a + L) - anchoredCyclicOffset n y a)
  have hb (a : ℤ) (L : ℕ) : Measurable (fun y => b y a L) :=
    measurable_const.mul ((measurable_anchoredCyclicOffset n _).sub
      (measurable_anchoredCyclicOffset n _))
  let B := fun y => 1 + R ^ 2 * ∑ r ∈ range n,
    (b y j (r + 1) ^ (-(2 : ℝ)) + b y (j + (r + 1 : ℕ))
      ((n + 1) - (r + 1)) ^ (-(2 : ℝ)))
  have hB : Measurable B := measurable_const.add (measurable_const.mul
    (Finset.measurable_sum _ fun r _ => ((hb _ _).pow_const _).add ((hb _ _).pow_const _)))
  have he (X : Configuration n.succPNat) (a : ℤ) (L : ℕ) :
      blockLength X a L = b (anchorCoords n X.val).2 a L := by
    simp only [blockLength, cyclicLift_eq_anchor_add, b]
    ring
  have h := (indepFun_cyclicLift_anchorCoords P n i).comp measurable_id hB
  have heq : (fun X : Configuration n.succPNat => microLocalRow R X j) =
      B ∘ (fun X => (anchorCoords n X.val).2) := by
    funext X
    change microLocalRow R X j = B ((anchorCoords n X.val).2)
    simp only [microLocalRow, Nat.succPNat_coe, Nat.succ_eq_add_one,
      Nat.add_sub_cancel, B, he]
  rw [heq]
  exact h

/-- The shifted inverse-square series is summable. -/
theorem microLocal_summable : Summable (fun r : ℕ => (r + 1 : ℝ) ^ (-(2 : ℝ))) := by
  have h := (Real.summable_nat_rpow.mpr (show -(2 : ℝ) < -1 by norm_num)).comp_injective
    (show Function.Injective (fun r : ℕ => r + 1) from fun a b h => Nat.add_right_cancel h)
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using h

/-- A positive constant controls the row moment uniformly in every label and size. -/
theorem microLocal_row_uniform (P : Parameters) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (N : ℕ+) (i : ℤ),
      ∃ _h : Integrable (fun X : Configuration N => microLocalRow R X i) (gibbsMeasure P N),
        (∫⁻ X : Configuration N, ENNReal.ofReal (microLocalRow R X i) ∂gibbsMeasure P N) ≤
          ENNReal.ofReal C := by
  obtain ⟨A, hA, hblocks⟩ := inverse_blocks_uniform P (show (0 : ℝ) < 2 by norm_num)
  let S := ∑' r : ℕ, (r + 1 : ℝ) ^ (-(2 : ℝ))
  have hS : 0 ≤ S := tsum_nonneg fun r => Real.rpow_nonneg (by positivity) _
  refine ⟨1 + R ^ 2 * (2 * A * S), by positivity, ?_⟩
  intro hPL N i
  let := (modelWellDefined P N).2.2
  have hi (j : ℤ) (L : ℕ) (hL : 0 < L) := (hblocks hPL N j L hL).choose
  have hb (j : ℤ) (L : ℕ) (hL : 0 < L) :
      (∫ X : Configuration N, blockLength X j L ^ (-(2 : ℝ)) ∂gibbsMeasure P N) ≤
        A * (L : ℝ) ^ (-(2 : ℝ)) := by
    have h := (hblocks hPL N j L hL).choose_spec
    rw [← ofReal_integral_eq_lintegral_ofReal (hi j L hL)
      (ae_of_all _ fun X => Real.rpow_nonneg (blockLength_pos X j hL).le _)] at h
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hA.le
      (Real.rpow_nonneg (by positivity) _))).mp h
  have hsum : Integrable (fun X : Configuration N =>
      ∑ r ∈ range ((N : ℕ) - 1), (blockLength X i (r + 1) ^ (-(2 : ℝ)) +
      blockLength X (i + (r + 1 : ℕ)) ((N : ℕ) - (r + 1)) ^ (-(2 : ℝ))))
      (gibbsMeasure P N) := by
    apply integrable_finsetSum
    intro r hr
    have hrN := mem_range.mp hr
    exact (hi _ _ (by omega)).add (hi _ _ (by omega))
  have hir : Integrable (fun X : Configuration N => microLocalRow R X i) (gibbsMeasure P N) :=
    (integrable_const 1).add (hsum.const_mul _)
  refine ⟨hir, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hir
    (ae_of_all _ fun X => microLocalRow_nonneg R X i)]
  apply ENNReal.ofReal_le_ofReal
  have hpartial : (∑ r ∈ range ((N : ℕ) - 1), (r + 1 : ℝ) ^ (-(2 : ℝ))) ≤ S :=
    microLocal_summable.sum_le_tsum _ (fun r _ => Real.rpow_nonneg (by positivity) _)
  have hreflect : (∑ r ∈ range ((N : ℕ) - 1),
      (((N : ℕ) - (r + 1) : ℕ) : ℝ) ^ (-(2 : ℝ))) =
      ∑ r ∈ range ((N : ℕ) - 1), (r + 1 : ℝ) ^ (-(2 : ℝ)) := by
    rw [← sum_range_reflect]
    apply sum_congr rfl
    intro r hr
    have hrN := mem_range.mp hr
    congr 1
    have he : (N : ℕ) - ((((N : ℕ) - 1) - 1 - r) + 1) = r + 1 := by omega
    rw [he]
    push_cast
    rfl
  change (∫ X : Configuration N, 1 + R ^ 2 * _ ∂gibbsMeasure P N) ≤ _
  rw [integral_add (integrable_const _) (hsum.const_mul _), integral_const,
    probReal_univ, one_smul, integral_const_mul,
    integral_finsetSum _ (fun r hr => by
      have hrN := mem_range.mp hr
      exact (hi _ _ (by omega)).add (hi _ _ (by omega)))]
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg R)
  calc
    _ ≤ ∑ r ∈ range ((N : ℕ) - 1), (A * (r + 1 : ℝ) ^ (-(2 : ℝ)) +
        A * (((N : ℕ) - (r + 1) : ℕ) : ℝ) ^ (-(2 : ℝ))) := by
      apply sum_le_sum
      intro r hr
      have hrN := mem_range.mp hr
      rw [integral_add (hi _ _ (by omega)) (hi _ _ (by omega))]
      exact add_le_add (by
        simpa only [Nat.cast_add, Nat.cast_one] using hb i (r + 1) (by omega))
        (hb (i + (r + 1 : ℕ)) ((N : ℕ) - (r + 1)) (by omega))
    _ = 2 * A * ∑ r ∈ range ((N : ℕ) - 1), (r + 1 : ℝ) ^ (-(2 : ℝ)) := by
      rw [sum_add_distrib, ← mul_sum, ← mul_sum, hreflect]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpartial (by positivity)

end Riesz1

end
