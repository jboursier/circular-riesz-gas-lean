/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.ExpectationBoundTransfer
public import Riesz1.ToMathlib.LogConcave.LinearTail

/-!
# Exponentially small centered expectation errors

The forcing error in Lemma 4.3 is dominated directly
by the exponential block moment.
-/

public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

/-- Any subblock has smaller microscopic span than the enclosing lifted block. -/
theorem blockLength_subblock_le {N : ℕ+} (X : Configuration N) (i j : ℤ) (L k : ℕ)
    (hij : i ≤ j) (hjk : j + (k : ℤ) ≤ i + (L : ℤ)) :
    blockLength X j k ≤ blockLength X i L := by
  have h1 := (cyclicLift_strictMono X).monotone hij
  have h2 := (cyclicLift_strictMono X).monotone hjk
  unfold blockLength
  have hNr : (0 : ℝ) ≤ (N : ℕ) := by positivity
  exact mul_le_mul_of_nonneg_left (by linarith) hNr

/-- Internal quantitative error bound at every positive forcing scale. -/
theorem expectation_error_exp_internal (hPL : External.PrekopaLeindler) (P : Parameters)
    (N : ℕ+) (hN : 2 ≤ (N : ℕ)) {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ)
    (i j : ℤ) (L k : ℕ) (hL : 0 < L) (hij : i ≤ j) (hjk : j + (k : ℤ) ≤ i + (L : ℤ))
    {R : ℝ} (hR : 0 < R) :
    |(∫ X : Configuration N, blockLength X j k ∂constrainedLaw P N θ i L R) - (k : ℝ)| ≤
      (constrainedNormalizer P N θ i L R)⁻¹ *
        (3 * (L : ℝ) * (2 / blockMomentExponent + 1) *
          Real.exp (-blockMomentExponent * (R / L) / 2)) := by
  let := isProbabilityMeasure_gibbsMeasure P N
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hkL : k ≤ L := by omega
  have hkLr : (k : ℝ) ≤ L := by exact_mod_cast hkL
  have hc := blockMomentExponent_pos
  let B := (L : ℝ) * (2 / blockMomentExponent + 1) * Real.exp (-blockMomentExponent * (R / L) / 2)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let G := fun X : Configuration N => (blockLength X j k - (k : ℝ)) *
    (Real.exp (-P.val.1 * forcingPotential θ i L R X) - 1)
  have hG := blockLength_constrained_centered_internal P N hN hθ i L hR j k
  change Integrable G (gibbsMeasure P N) ∧ _ at hG
  have hb (X : Configuration N) : |G X| ≤ B *
      Real.exp (blockMomentExponent * (blockLength X i L / L)) := by
    by_cases hS : blockLength X i L ≤ R
    · dsimp only [G]
      rw [forcingPotential_eq_zero hθ hR i L X hS]
      simp only [mul_zero, Real.exp_zero, sub_self, mul_zero, abs_zero]
      positivity
    · have hS' : R < blockLength X i L := lt_of_not_ge hS
      have hA0 : 0 ≤ blockLength X j k := by
        rw [blockLength_eq_sum]; exact Finset.sum_nonneg fun r _ => (gap_pos X _).le
      have hAS := blockLength_subblock_le X i j L k hij hjk
      have hSk : |blockLength X j k - (k : ℝ)| ≤ blockLength X i L + (L : ℝ) :=
        abs_le.mpr ⟨by linarith, by linarith⟩
      have hw := exp_neg_forcingPotential_le_one P hθ hR N i L X
      have hw0 := Real.exp_pos (-P.val.1 * forcingPotential θ i L R X)
      have hwe : |Real.exp (-P.val.1 * forcingPotential θ i L R X) - 1| ≤ 1 :=
        abs_le.mpr ⟨by linarith, by linarith⟩
      have he := linear_tail_le_exp blockMomentExponent_pos
        (div_nonneg (blockLength_pos X i hL).le hLr.le)
        (div_le_div_of_nonneg_right hS'.le hLr.le)
      have hscale := mul_le_mul_of_nonneg_left he hLr.le
      have hcancel : (L : ℝ) * (blockLength X i L / L + 1) = blockLength X i L + L := by field_simp
      rw [hcancel] at hscale
      calc |G X| ≤ |blockLength X j k - (k : ℝ)| * 1 := by
              dsimp only [G]
              rw [abs_mul]
              exact mul_le_mul_of_nonneg_left hwe (abs_nonneg _)
        _ ≤ blockLength X i L + (L : ℝ) := by simpa only [mul_one] using hSk
        _ ≤ (L : ℝ) * ((2 / blockMomentExponent + 1) *
              Real.exp (blockMomentExponent * (blockLength X i L / L)) *
              Real.exp (-blockMomentExponent * (R / L) / 2)) := hscale
        _ = B * Real.exp (blockMomentExponent * (blockLength X i L / L)) := by dsimp [B]; ring
  have he := blockLength_exp_moment hPL P N hN i L hL
  have hbound := integral_mono hG.1.abs (he.1.const_mul B) hb
  rw [integral_const_mul] at hbound
  have hnorm : |∫ X, G X ∂gibbsMeasure P N| ≤ 3 * B :=
    (abs_integral_le_integral_abs).trans (hbound.trans (by nlinarith [he.2]))
  rw [hG.2, abs_mul, abs_of_pos (inv_pos.mpr (constrainedNormalizer_mem_Ioc P N hθ hR i L).1)]
  have hh := mul_le_mul_of_nonneg_left hnorm
    (inv_nonneg.mpr (constrainedNormalizer_mem_Ioc P N hθ hR i L).1.le)
  convert hh using 1
  dsimp only [B]
  ring

end Riesz1

end
