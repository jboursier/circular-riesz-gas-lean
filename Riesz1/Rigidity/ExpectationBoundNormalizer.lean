/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.ExpectationNormalizer

/-!
# Positive normalizer bounds at all block sizes

The small-size and large-size bounds needed in Lemma 4.3.
Every bound is uniform over admissible cutoffs.
-/

public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

/-- The first moment alone gives the useful lower bound `z ≥ 1 - L/R`. -/
theorem constrainedNormalizer_ge_one_sub_div (P : Parameters) (N : ℕ+)
    (hN : 2 ≤ (N : ℕ)) {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ)
    (i : ℤ) (L : ℕ) {R : ℝ} (hR : 0 < R) :
    1 - (L : ℝ) / R ≤ constrainedNormalizer P N θ i L R := by
  let := isProbabilityMeasure_gibbsMeasure P N
  have hm := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all (gibbsMeasure P N) (fun X : Configuration N =>
      (blockLength_eq_sum X i L ▸ Finset.sum_nonneg (fun r _ => (gap_pos X _).le))))
    (integrable_blockLength P N i L) R
  rw [integral_blockLength_gibbsMeasure P N hN] at hm
  have he : (gibbsMeasure P N).real {X | R < blockLength X i L} ≤ (L : ℝ) / R := by
    apply (le_div_iff₀ hR).mpr
    have hh := measureReal_mono (μ := gibbsMeasure P N)
      (show {X : Configuration N | R < blockLength X i L} ⊆ {X | R ≤ blockLength X i L} from
        fun X h => (show R < blockLength X i L from h).le)
    nlinarith [mul_le_mul_of_nonneg_left hh hR.le]
  have hz := one_sub_constrainedNormalizer_le_block_tail P N hθ i L hR
  linarith

/-- A cutoff-independent positive denominator for every `L ≥ 2`. -/
theorem constrainedNormalizer_ge_two (P : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) (i : ℤ) {L : ℕ} (hL : 2 ≤ L)
    {γ : ℝ} (hγ : 0 < γ) :
    1 - (2 : ℝ) ^ (-γ) ≤ constrainedNormalizer P N θ i L ((L : ℝ) ^ (1 + γ)) := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hz := constrainedNormalizer_ge_one_sub_div P N hN hθ i L
    (Real.rpow_pos_of_pos hLr (1 + γ))
  have he : (L : ℝ) / (L : ℝ) ^ (1 + γ) = (L : ℝ) ^ (-γ) := by
    nth_rw 1 [← Real.rpow_one (L : ℝ)]
    rw [← Real.rpow_sub hLr]
    congr 1
    ring
  rw [he] at hz
  have hh := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 2)
    (by exact_mod_cast hL : (2 : ℝ) ≤ L) (neg_nonpos.mpr hγ.le)
  linarith

/-- On a one-gap block the pair sum is exactly twice the cutoff of that gap. -/
theorem forcingPotential_one_gap {N : ℕ+} (θ : ℝ → ℝ) (i : ℤ) (R : ℝ) (X : Configuration N) :
    forcingPotential θ i 1 R X = 2 * θ (gap X i / R) := by
  have hcc : Finset.Icc i (i + 1) = {i, i + 1} := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hoc : Finset.Ioc i (i + 1) = {i + 1} := by
    ext k
    simp only [Finset.mem_Ioc, Finset.mem_singleton]
    omega
  have hnot : i ∉ ({i + 1} : Finset ℤ) := by
    simpa only [Finset.mem_singleton] using (show i ≠ i + 1 by omega)
  rw [forcingPotential, Nat.cast_one, hcc, Finset.sum_insert hnot,
    Finset.sum_singleton, hoc, Finset.sum_singleton, Finset.Ioc_self, Finset.sum_empty, add_zero]
  rfl

/-- The missing smallest-block denominator: it holds for every admissible cutoff. -/
theorem constrainedNormalizer_ge_one_gap (P : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) (i : ℤ) :
    Real.exp (-2 * P.val.1) / 2 ≤ constrainedNormalizer P N θ i 1 1 := by
  let := isProbabilityMeasure_gibbsMeasure P N
  let E : Set (Configuration N) := {X | gap X i ≤ 2}
  have hE : MeasurableSet E := measurableSet_le (measurable_gap i) measurable_const
  have hm := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all (gibbsMeasure P N) (fun X : Configuration N => (gap_pos X i).le))
    (integrable_gap P N i) (2 : ℝ)
  rw [integral_gap_gibbsMeasure P N hN] at hm
  have hEc : (gibbsMeasure P N).real Eᶜ ≤ 1 / 2 := by
    have hh : Eᶜ ⊆ {X | (2 : ℝ) ≤ gap X i} := fun X hX => (lt_of_not_ge (show ¬ gap X i ≤ 2 from hX)).le
    have hi := measureReal_mono (μ := gibbsMeasure P N) hh
    linarith
  have hhalf : 1 / 2 ≤ (gibbsMeasure P N).real E := by
    have hh := measureReal_add_measureReal_compl (μ := gibbsMeasure P N) hE
    rw [probReal_univ] at hh
    linarith
  have hcut := cutoff_bounds (hθ.1.of_le (by simp)) hθ.2.1 hθ.2.2.2.1
  have hF (X : Configuration N) (hX : X ∈ E) : forcingPotential θ i 1 1 X ≤ 2 := by
    rw [forcingPotential_one_gap, div_one]
    have hmon := hcut.1 (gap_pos X i).le (by norm_num : (0 : ℝ) ≤ 2) hX
    linarith [hcut.2.2.2.2.2]
  have hw := integrable_exp_neg_forcingPotential P N hθ (by norm_num : (0 : ℝ) < 1) i 1
  have hi : Integrable (E.indicator (fun _ => Real.exp (-2 * P.val.1))) (gibbsMeasure P N) :=
    (integrable_const (Real.exp (-2 * P.val.1))).indicator hE
  have hh := integral_mono hi hw (fun X => show E.indicator (fun _ => Real.exp (-2 * P.val.1)) X ≤
      Real.exp (-P.val.1 * forcingPotential θ i 1 1 X) from by
    by_cases hX : X ∈ E
    · rw [Set.indicator_of_mem hX]
      exact Real.exp_le_exp.mpr (by nlinarith [hF X hX, P.2.1])
    · rw [Set.indicator_of_notMem hX]
      exact (Real.exp_pos _).le)
  rw [integral_indicator hE, setIntegral_const, smul_eq_mul] at hh
  change _ ≤ constrainedNormalizer P N θ i 1 1 at hh
  nlinarith [Real.exp_pos (-2 * P.val.1)]

end Riesz1

end
