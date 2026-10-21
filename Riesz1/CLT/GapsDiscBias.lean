/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.GapsDiscInversion

/-!
# Telescoping identities for selection bias

The two deterministic identities used in the proof of
Corollary 1, with arbitrary starting label.
The final lemmas check inversion and exact absence of bias for two particles.
-/

@[expose] public section

noncomputable section

open MeasureTheory Finset

namespace Riesz1

variable {N : ℕ+}

lemma sum_selectionWeight_blockLength (X : Configuration N) (i : ℤ) (m : ℕ) :
    ∑ j ∈ range m, selectionWeight X (i + j) =
      (blockLength X (i - 1) m + blockLength X i m) / 2 := by
  rw [blockLength_eq_sum, blockLength_eq_sum, ← sum_add_distrib, sum_div]
  apply sum_congr rfl
  intro j _
  unfold selectionWeight
  rw [show i + (j : ℤ) - 1 = i - 1 + j by ring]

lemma blockLength_shift_sub (X : Configuration N) (i : ℤ) (j k : ℕ) :
    blockLength X (i + j) k - blockLength X i k =
      blockLength X (i + k) j - blockLength X i j := by
  unfold blockLength
  rw [show i + (j : ℤ) + k = i + k + j by ring]
  ring

lemma centeredGap_shift_sub (s : RieszExponent) (X : Configuration N) (i : ℤ)
    (j k : ℕ) (hk : 1 ≤ k ∧ k ≤ (N : ℕ) / 2) :
    centeredGap s X (i + j) k hk - centeredGap s X i k hk =
      ((blockLength X (i + k) j - j) - (blockLength X i j - j)) / gapScale s N k := by
  unfold centeredGap
  rw [← sub_div]
  congr 1
  have h := blockLength_shift_sub X i j k
  linarith

/-- For two particles the Voronoi cells have equal lengths, irrespective of the gaps. -/
lemma selectionWeight_two (hN : (N : ℕ) = 2) (X : Configuration N) (i : ℤ) :
    selectionWeight X i = 1 := by
  have h := blockLength_N X (i - 1)
  rw [hN] at h
  norm_num [blockLength_eq_sum, sum_range_succ] at h
  unfold selectionWeight
  linarith

/-- The `N = 2`, `r = 1` check on the moment statement is pointwise. -/
lemma centeredBlock_square_two (hN : (N : ℕ) = 2) (X : Configuration N) (i : ℤ) :
    (blockLength X i 1 - 1) ^ 2 ≤ 1 := by
  have hlo := (gap_pos X i).le
  have hhi := gap_le_N X i
  rw [hN] at hhi
  norm_num at hhi
  have hprod := mul_nonneg hlo (sub_nonneg.mpr hhi)
  simpa [blockLength_eq_sum] using (show (gap X i - 1) ^ 2 ≤ 1 by nlinarith)

/-- The requested `N = 2`, `k = 1` check on the inversion statement. -/
lemma selectedDiscrepancy_two (hN : (N : ℕ) = 2) (X : Configuration N) :
    0 ≤ selectedDiscrepancy X 1 (by omega) ↔ gap X (nearestLabel X) ≤ 1 := by
  have h := selectedDiscrepancy_ge_iff X 1 (by omega) 0 (by norm_num) (by omega)
  simpa [blockLength_eq_sum] using h

/-- The requested `N = 2` check on bias removal: the bias is exactly zero. -/
lemma selectionBias_two (hN : (N : ℕ) = 2) (P : Parameters)
    (F : Configuration N → ℝ) :
    |(∫ X, selectionWeight X 0 * F X ∂gibbsMeasure P N) -
      ∫ X, F X ∂gibbsMeasure P N| = 0 := by
  simp only [selectionWeight_two hN, one_mul, sub_self, abs_zero]

end Riesz1

end
end
