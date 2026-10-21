/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.GapLawSymmetry

/-!
# First moments of gaps and block lengths

The expectation assertions of Lemma 4.2.
Cyclic symmetry and the deterministic sum of a full period give unit mean
for every gap. All integrals are shown to be integrable first.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

namespace Riesz1

lemma gap_le_N {N : ℕ+} (X : Configuration N) (j : ℤ) :
    gap X j ≤ ((N : ℕ) : ℝ) := by
  have hN : (0 : ℝ) ≤ ((N : ℕ) : ℝ) := by positivity
  have h := (cyclicLift_strictMono X).monotone
    (show j + 1 ≤ j + ((N : ℕ) : ℤ) by have := N.pos; omega)
  rw [cyclicLift_add_N] at h
  unfold gap
  nlinarith

/-- Every gap is bounded, hence integrable under the Gibbs probability. -/
theorem integrable_gap (P : Parameters) (N : ℕ+) (j : ℤ) :
    Integrable (fun X : Configuration N => gap X j) (gibbsMeasure P N) := by
  have := (modelWellDefined P N).2.2
  apply Integrable.of_bound (measurable_gap j).aestronglyMeasurable ((N : ℕ) : ℝ)
  exact ae_of_all _ fun X => by
    rw [Real.norm_eq_abs, abs_of_pos (gap_pos X j)]
    exact gap_le_N X j

theorem integrable_blockLength (P : Parameters) (N : ℕ+) (j : ℤ) (L : ℕ) :
    Integrable (fun X : Configuration N => blockLength X j L) (gibbsMeasure P N) := by
  simp only [blockLength_eq_sum]
  exact integrable_finsetSum _ fun r _ => integrable_gap P N (j + r)

/-- The distribution of a gap does not depend on its integer label. -/
theorem map_gap_gibbsMeasure_eq (P : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (j : ℤ) :
    (gibbsMeasure P N).map (fun X => gap X j) =
      (gibbsMeasure P N).map (fun X => gap X 0) := by
  refine Int.induction_on j rfl ?_ ?_
  · intro k ih
    exact (map_gap_add_one_gibbsMeasure P N hN k).trans ih
  · intro k ih
    have h := map_gap_add_one_gibbsMeasure P N hN (-(k : ℤ) - 1)
    rw [sub_add_cancel] at h
    exact h.symm.trans ih

lemma integral_gap_eq_zero_label (P : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (j : ℤ) :
    (∫ X : Configuration N, gap X j ∂gibbsMeasure P N) =
      ∫ X : Configuration N, gap X 0 ∂gibbsMeasure P N := by
  change (∫ X : Configuration N, id (gap X j) ∂gibbsMeasure P N) =
    ∫ X : Configuration N, id (gap X 0) ∂gibbsMeasure P N
  rw [← integral_map (measurable_gap j).aemeasurable measurable_id.aestronglyMeasurable,
    ← integral_map (measurable_gap 0).aemeasurable measurable_id.aestronglyMeasurable,
    map_gap_gibbsMeasure_eq P N hN j]

/-- **Unit mean of every gap**, part of Lemma 4.2. -/
theorem integral_gap_gibbsMeasure (P : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (j : ℤ) :
    (∫ X : Configuration N, gap X j ∂gibbsMeasure P N) = 1 := by
  have := (modelWellDefined P N).2.2
  have hsum : (∑ i ∈ Finset.range (N : ℕ),
      ∫ X : Configuration N, gap X (i : ℤ) ∂gibbsMeasure P N) = ((N : ℕ) : ℝ) := by
    rw [← integral_finsetSum (Finset.range (N : ℕ)) (fun (i : ℕ) _ => integrable_gap P N (i : ℤ))]
    simp only [sum_gap_eq]
    simp
  simp only [integral_gap_eq_zero_label P N hN] at hsum
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hpos : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
  rw [integral_gap_eq_zero_label P N hN j]
  nlinarith

/-- **Mean block length**, in fact for every nonnegative integer block length. -/
theorem integral_blockLength_gibbsMeasure (P : Parameters) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) (j : ℤ) (L : ℕ) :
    (∫ X : Configuration N, blockLength X j L ∂gibbsMeasure P N) = (L : ℝ) := by
  simp only [blockLength_eq_sum]
  rw [integral_finsetSum (Finset.range L) (fun (r : ℕ) _ => integrable_gap P N (j + (r : ℤ)))]
  simp [integral_gap_gibbsMeasure P N hN]

end Riesz1

end
end
