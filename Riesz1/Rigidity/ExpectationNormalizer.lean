/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.BlockMoments
public import Riesz1.Rigidity.ForcingComparison

/-!
# Cutoff-independent normalizer estimates

Inputs to Lemma 4.3: the loss of mass under
convexification is bounded by the exponentially small block tail.
The estimates hold for every admissible forcing cutoff.
-/

public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

/-- Convexification loses at most the probability that the forcing is active. -/
theorem one_sub_constrainedNormalizer_le_block_tail (P : Parameters) (N : ℕ+)
    {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) (i : ℤ) (L : ℕ) {R : ℝ} (hR : 0 < R) :
    1 - constrainedNormalizer P N θ i L R ≤
      (gibbsMeasure P N).real {X | R < blockLength X i L} := by
  have := isProbabilityMeasure_gibbsMeasure P N
  let E : Set (Configuration N) := {X | R < blockLength X i L}
  have hE : MeasurableSet E := measurableSet_lt measurable_const (measurable_blockLength i L)
  have hw := integrable_exp_neg_forcingPotential P N hθ hR i L
  have hind : Integrable (E.indicator (fun _ => (1 : ℝ))) (gibbsMeasure P N) :=
    (integrable_const (1 : ℝ)).indicator hE
  have hb (X : Configuration N) :
      1 - Real.exp (-P.val.1 * forcingPotential θ i L R X) ≤ E.indicator (fun _ => (1 : ℝ)) X := by
    by_cases hX : X ∈ E
    · rw [Set.indicator_of_mem hX]
      linarith [Real.exp_pos (-P.val.1 * forcingPotential θ i L R X)]
    · rw [Set.indicator_of_notMem hX,
        forcingPotential_eq_zero hθ hR i L X (not_lt.mp hX)]
      simp
  have hi := integral_mono ((integrable_const (1 : ℝ)).sub hw) hind hb
  simp only [Pi.sub_apply] at hi
  rw [integral_sub (integrable_const (1 : ℝ)) hw, integral_indicator hE] at hi
  simpa only [integral_const, probReal_univ, smul_eq_mul, mul_one, Measure.real,
    Measure.restrict_apply MeasurableSet.univ, univ_inter, measure_univ, ENNReal.toReal_one,
    constrainedNormalizer, E] using hi

/-- An exponential bound for the activation event, uniformly over cutoffs. -/
theorem forcing_activation_tail (hPL : External.PrekopaLeindler) (P : Parameters)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ)
    (i : ℤ) (L : ℕ) (hL : 0 < L) {R : ℝ} (hR : 0 < R) :
    (gibbsMeasure P N).real {X | 0 < forcingPotential θ i L R X} ≤
      3 * Real.exp (-blockMomentExponent * (R / L)) := by
  have := isProbabilityMeasure_gibbsMeasure P N
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hsub : (gibbsMeasure P N).real {X | 0 < forcingPotential θ i L R X} ≤
      (gibbsMeasure P N).real {X | R < blockLength X i L} :=
    measureReal_mono fun X hX => blockLength_gt_of_forcingPotential_pos hθ hR i L X hX
  have ht := blockLength_upper_tail hPL P N hN i L hL (R / L)
  rw [mul_div_cancel₀ R hLr.ne'] at ht
  exact hsub.trans ht

/-- The quantitative normalizer lower bound used for large blocks in
Lemma 4.3, with no dependence on the cutoff. -/
theorem constrainedNormalizer_ge_one_sub_exp (hPL : External.PrekopaLeindler)
    (P : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ)
    (i : ℤ) (L : ℕ) (hL : 0 < L) (γ : ℝ) :
    1 - 3 * Real.exp (-blockMomentExponent * (L : ℝ) ^ γ) ≤
      constrainedNormalizer P N θ i L ((L : ℝ) ^ (1 + γ)) := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hR := Real.rpow_pos_of_pos hLr (1 + γ)
  have hz := one_sub_constrainedNormalizer_le_block_tail P N hθ i L hR
  have ht := blockLength_upper_tail hPL P N hN i L hL ((L : ℝ) ^ γ)
  have he : (L : ℝ) * (L : ℝ) ^ γ = (L : ℝ) ^ (1 + γ) := by
    rw [Real.rpow_add hLr, Real.rpow_one]
  rw [he] at ht
  linarith

end Riesz1

end
