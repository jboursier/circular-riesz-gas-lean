/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.ExpectationBoundTransfer
public import Riesz1.ToMathlib.LogConcave.EventSecondMoment

/-!
# Exponentially small centered expectation errors

The quadratic block moment and Cauchy--Schwarz control the forcing error
in Lemma 4.3 on the event where the forcing is active.
-/

public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

/-- Centering a block length preserves its quadratic moment bound. -/
theorem blockLength_centered_second_moment :
    ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (P : Parameters)
      (N : ℕ+) (_hN : 2 ≤ (N : ℕ)) (j : ℤ) (k : ℕ), 0 < k →
      Integrable (fun X : Configuration N => (blockLength X j k - (k : ℝ)) ^ 2)
        (gibbsMeasure P N) ∧
      (∫ X : Configuration N, (blockLength X j k - (k : ℝ)) ^ 2
        ∂gibbsMeasure P N) ≤ C * (k : ℝ) ^ 2 := by
  obtain ⟨C, hC, hb⟩ := blockLength_moments 2 (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro hPL P N hN j k hk
  let := isProbabilityMeasure_gibbsMeasure P N
  obtain ⟨hi, hm⟩ := hb hPL P N hN j k hk
  simp only [Real.rpow_two] at hi hm
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all _ fun X => sq_nonneg (blockLength X j k))] at hm
  have hsecond := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ C * (k : ℝ) ^ 2)).mp hm
  have hmean := integrable_blockLength P N j k
  have he (X : Configuration N) : (blockLength X j k - (k : ℝ)) ^ 2 =
      blockLength X j k ^ 2 - (2 * (k : ℝ)) * blockLength X j k + (k : ℝ) ^ 2 := by ring
  have hc : Integrable (fun X : Configuration N => (blockLength X j k - (k : ℝ)) ^ 2)
      (gibbsMeasure P N) :=
    ((hi.sub (hmean.const_mul (2 * (k : ℝ)))).add (integrable_const ((k : ℝ) ^ 2))).congr
      (ae_of_all _ fun X => (he X).symm)
  have hsub : Integrable (fun X : Configuration N =>
      blockLength X j k ^ 2 - (2 * (k : ℝ)) * blockLength X j k) (gibbsMeasure P N) :=
    hi.sub (hmean.const_mul _)
  refine ⟨hc, ?_⟩
  simp_rw [he]
  rw [integral_add hsub (integrable_const ((k : ℝ) ^ 2)),
    integral_sub hi (hmean.const_mul (2 * (k : ℝ))), integral_const_mul,
    integral_blockLength_gibbsMeasure P N hN, integral_const, probReal_univ, one_smul]
  nlinarith [sq_nonneg (k : ℝ)]

/-- The centered density error is bounded by Cauchy--Schwarz on the activation event. -/
theorem expectation_error_cauchy_schwarz_internal :
    ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (P : Parameters)
      (N : ℕ+) (_hN : 2 ≤ (N : ℕ)) (θ : ℝ → ℝ), IsForcingCutoff θ →
      ∀ (i j : ℤ) (L k : ℕ), 0 < L → 0 < k → ∀ R : ℝ, 0 < R →
      |(∫ X : Configuration N, blockLength X j k ∂constrainedLaw P N θ i L R) - (k : ℝ)| ≤
        (constrainedNormalizer P N θ i L R)⁻¹ *
          (C * (k : ℝ) * Real.exp (-blockMomentExponent * (R / L) / 2)) := by
  obtain ⟨B, hB, hb⟩ := blockLength_centered_second_moment
  refine ⟨B ^ (1 / (2 : ℝ)) * (3 : ℝ) ^ (1 / (2 : ℝ)), by positivity, ?_⟩
  intro hPL P N hN θ hθ i j L k hL hk R hR
  let := isProbabilityMeasure_gibbsMeasure P N
  let E : Set (Configuration N) := {X | 0 < forcingPotential θ i L R X}
  have hE : MeasurableSet E := measurableSet_lt measurable_const (measurable_forcingPotential hθ i L R)
  let Y := fun X : Configuration N => |blockLength X j k - (k : ℝ)|
  let G := fun X : Configuration N => (blockLength X j k - (k : ℝ)) *
    (Real.exp (-P.val.1 * forcingPotential θ i L R X) - 1)
  have hG := blockLength_constrained_centered_internal P N hN hθ i L hR j k
  change Integrable G (gibbsMeasure P N) ∧ _ at hG
  obtain ⟨hi, hm⟩ := hb hPL P N hN j k hk
  have hY : Integrable (fun X => Y X ^ 2) (gibbsMeasure P N) := by
    simpa only [Y, sq_abs] using hi
  have hYi : Integrable Y (gibbsMeasure P N) :=
    ((integrable_blockLength P N j k).sub (integrable_const (k : ℝ))).abs
  have hpoint (X : Configuration N) : |G X| ≤ E.indicator Y X := by
    by_cases hX : X ∈ E
    · rw [Set.indicator_of_mem hX]
      have hw := exp_neg_forcingPotential_le_one P hθ hR N i L X
      have hw0 := Real.exp_pos (-P.val.1 * forcingPotential θ i L R X)
      have hwe : |Real.exp (-P.val.1 * forcingPotential θ i L R X) - 1| ≤ 1 :=
        abs_le.mpr ⟨by linarith, by linarith⟩
      exact (abs_mul _ _).le.trans (by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hwe (abs_nonneg (blockLength X j k - (k : ℝ))))
    · have hF : forcingPotential θ i L R X = 0 := le_antisymm (not_lt.mp hX)
        (forcingPotential_nonneg hθ hR i L X)
      simp only [G, hF, mul_zero, Real.exp_zero, sub_self, abs_zero,
        Set.indicator_of_notMem hX, le_refl]
  have hcs := integral_on_event_le_second_moment
    hYi.aestronglyMeasurable
    (fun X : Configuration N => abs_nonneg (blockLength X j k - (k : ℝ))) hY hE
  have htail := forcing_activation_tail hPL P N hN hθ i L hL hR
  have hmoment : (∫ X, Y X ^ 2 ∂gibbsMeasure P N) ^ (1 / (2 : ℝ)) ≤
      B ^ (1 / (2 : ℝ)) * (k : ℝ) := by
    have hh := Real.rpow_le_rpow (integral_nonneg fun X => sq_nonneg (Y X))
      (show (∫ X, Y X ^ 2 ∂gibbsMeasure P N) ≤ B * (k : ℝ) ^ 2 by
        simpa only [Y, sq_abs] using hm) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [Real.mul_rpow hB.le (sq_nonneg _),
      ← Real.rpow_natCast_mul (by positivity : (0 : ℝ) ≤ k) 2] at hh
    norm_num only [Nat.cast_ofNat, mul_one_div_cancel, Real.rpow_one] at hh
    exact hh
  have hprob : (gibbsMeasure P N).real E ^ (1 / (2 : ℝ)) ≤
      (3 : ℝ) ^ (1 / (2 : ℝ)) * Real.exp (-blockMomentExponent * (R / L) / 2) := by
    have hh := Real.rpow_le_rpow measureReal_nonneg htail (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [Real.mul_rpow (by norm_num) (Real.exp_pos _).le, ← Real.exp_mul] at hh
    have heq : (-blockMomentExponent * (R / L)) * (1 / (2 : ℝ)) =
        -blockMomentExponent * (R / L) / 2 := by ring
    rw [heq] at hh
    exact hh
  have hnum : |∫ X, G X ∂gibbsMeasure P N| ≤
      (B ^ (1 / (2 : ℝ)) * (3 : ℝ) ^ (1 / (2 : ℝ))) * (k : ℝ) *
        Real.exp (-blockMomentExponent * (R / L) / 2) := by
    calc |∫ X, G X ∂gibbsMeasure P N| ≤ ∫ X, |G X| ∂gibbsMeasure P N :=
          abs_integral_le_integral_abs
      _ ≤ ∫ X, E.indicator Y X ∂gibbsMeasure P N :=
        integral_mono hG.1.abs (hYi.indicator hE) hpoint
      _ = ∫ X in E, Y X ∂gibbsMeasure P N := integral_indicator hE
      _ ≤ (∫ X, Y X ^ 2 ∂gibbsMeasure P N) ^ (1 / (2 : ℝ)) *
          (gibbsMeasure P N).real E ^ (1 / (2 : ℝ)) := hcs
      _ ≤ (B ^ (1 / (2 : ℝ)) * (k : ℝ)) *
          ((3 : ℝ) ^ (1 / (2 : ℝ)) * Real.exp (-blockMomentExponent * (R / L) / 2)) :=
        mul_le_mul hmoment hprob (by positivity) (by positivity)
      _ = _ := by ring
  have hz := (constrainedNormalizer_mem_Ioc P N hθ hR i L).1
  rw [hG.2, abs_mul, abs_of_pos (inv_pos.mpr hz)]
  exact mul_le_mul_of_nonneg_left hnum (inv_nonneg.mpr hz.le)

end Riesz1

end
