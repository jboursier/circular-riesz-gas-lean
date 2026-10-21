/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Frozen.Variance
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Variance of a finite sum of square-integrable variables

For square-integrable real random variables `F_1, …, F_m` on a finite measure space, the variance
of the sum `F_1 + ⋯ + F_m` is at most `m` times the sum of the variances `Var F_j`. The proof
uses the Cauchy–Schwarz bound `(a_1 + ⋯ + a_m)² ≤ m (a_1² + ⋯ + a_m²)` for the centred summands.
This is the variance step of Proposition 5.9.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace Riesz1

/-- For a finite family of square-integrable real random variables `F j` on a finite measure
space, the variance of their sum is at most `m` times the sum of their variances. The sum is
integrable, and the statement asserts this integrability. -/
theorem variance_finsetSum_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (m : ℕ) (F : Fin m → Ω → ℝ) (hF : ∀ j, MemLp (F j) 2 μ) :
    ∃ hS : Integrable (fun ω => ∑ j, F j ω) μ,
      variance μ (fun ω => ∑ j, F j ω) hS ≤
        (m : ℝ≥0∞) * ∑ j, variance μ (F j) ((hF j).integrable one_le_two) := by
  have hint : ∀ j, Integrable (F j) μ := fun j => (hF j).integrable one_le_two
  have hS : Integrable (fun ω => ∑ j, F j ω) μ := integrable_finsetSum _ fun j _ => hint j
  refine ⟨hS, ?_⟩
  -- The mean of the sum is the sum of the means,
  -- so the centred sum is the sum of the centred terms.
  have hmean : ∫ ω, ∑ j, F j ω ∂μ = ∑ j, ∫ ω, F j ω ∂μ := integral_finsetSum _ fun j _ => hint j
  have hcentre : ∀ ω, ∑ j, F j ω - ∫ ω', ∑ j', F j' ω' ∂μ = ∑ j, (F j ω - ∫ ω', F j ω' ∂μ) := by
    intro ω
    rw [hmean, Finset.sum_sub_distrib]
  -- Pointwise bound on the squared centred sum.
  have hpt : ∀ ω, ENNReal.ofReal ((∑ j, F j ω - ∫ ω', ∑ j', F j' ω' ∂μ) ^ 2) ≤
      (m : ℝ≥0∞) * ∑ j, ENNReal.ofReal ((F j ω - ∫ ω', F j ω' ∂μ) ^ 2) := by
    intro ω
    have hcs : (∑ j, (F j ω - ∫ ω', F j ω' ∂μ)) ^ 2 ≤
        (m : ℝ) * ∑ j, (F j ω - ∫ ω', F j ω' ∂μ) ^ 2 := by
      have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
        (f := fun j => F j ω - ∫ ω', F j ω' ∂μ)
      simpa using h
    rw [hcentre ω]
    calc ENNReal.ofReal ((∑ j, (F j ω - ∫ ω', F j ω' ∂μ)) ^ 2)
        ≤ ENNReal.ofReal ((m : ℝ) * ∑ j, (F j ω - ∫ ω', F j ω' ∂μ) ^ 2) :=
          ENNReal.ofReal_le_ofReal hcs
      _ = ENNReal.ofReal (m : ℝ) * ENNReal.ofReal (∑ j, (F j ω - ∫ ω', F j ω' ∂μ) ^ 2) :=
          ENNReal.ofReal_mul (Nat.cast_nonneg m)
      _ = (m : ℝ≥0∞) * ∑ j, ENNReal.ofReal ((F j ω - ∫ ω', F j ω' ∂μ) ^ 2) := by
          rw [ENNReal.ofReal_natCast,
            ENNReal.ofReal_sum_of_nonneg (fun j _ => sq_nonneg _)]
  -- Integrate the pointwise bound and move the constant and the sum outside.
  unfold variance
  calc ∫⁻ ω, ENNReal.ofReal ((∑ j, F j ω - ∫ ω', ∑ j', F j' ω' ∂μ) ^ 2) ∂μ
      ≤ ∫⁻ ω, (m : ℝ≥0∞) * ∑ j, ENNReal.ofReal ((F j ω - ∫ ω', F j ω' ∂μ) ^ 2) ∂μ :=
        lintegral_mono hpt
    _ = (m : ℝ≥0∞) * ∑ j, ∫⁻ ω, ENNReal.ofReal ((F j ω - ∫ ω', F j ω' ∂μ) ^ 2) ∂μ := by
        rw [lintegral_const_mul' _ _ (ENNReal.natCast_ne_top m), lintegral_finsetSum']
        exact fun j _ => (((hint j).aemeasurable.sub_const _).pow_const 2).ennreal_ofReal

end Riesz1

end
