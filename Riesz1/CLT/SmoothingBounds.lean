/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.SmoothingStatistics
public import Riesz1.Variance.QuantitativeVarianceUniformConclusion

/-! # Normalization of the quantitative variance error -/

public section

open MeasureTheory
open scoped ENNReal

namespace Riesz1.Internal

/-- Normalize a centered variance estimate, retaining the exact maximum
of the two exponents. This is an internal algebraic helper. -/
lemma smoothing_scaled_second_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {H : Ω → ℝ}
    (hH : MemLp H 2 μ) (hmean : ∫ X, H X ∂μ = 0)
    {K s α ε C σ : ℝ} (hK : 0 < K)
    (herr : |(variance μ H (hH.integrable one_le_two)).toReal - K ^ s * σ| ≤
      C * K ^ (max (2 * s - 1) (2 * α) + ε)) :
    (∫ X, (K ^ (-s / 2) * H X) ^ 2 ∂μ) ≤
      σ + C * K ^ (max (s - 1) (2 * α - s) + ε) := by
  have hV : (variance μ H (hH.integrable one_le_two)).toReal = ∫ X, H X ^ 2 ∂μ := by
    unfold variance
    rw [hmean]
    simp only [sub_zero]
    rw [← ofReal_integral_eq_lintegral_ofReal hH.integrable_sq
      (Filter.Eventually.of_forall fun X => sq_nonneg (H X)),
      ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)]
  have hscale : (K ^ (-s / 2)) ^ 2 = K ^ (-s) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hK.le]
    congr 1
    push_cast
    ring
  have hmain : K ^ (-s) * K ^ s = 1 := by rw [← Real.rpow_add hK]; simp
  have hexp : -s + (max (2 * s - 1) (2 * α) + ε) =
      max (s - 1) (2 * α - s) + ε := by
    rw [show -s + (max (2 * s - 1) (2 * α) + ε) =
      (max (2 * s - 1) (2 * α) - s) + ε by ring, ← max_sub_sub_right]
    congr 2
    ring
  have hpow : K ^ (-s) * K ^ (max (2 * s - 1) (2 * α) + ε) =
      K ^ (max (s - 1) (2 * α - s) + ε) := by rw [← Real.rpow_add hK, hexp]
  calc (∫ X, (K ^ (-s / 2) * H X) ^ 2 ∂μ)
      = K ^ (-s) * (variance μ H (hH.integrable one_le_two)).toReal := by
        simp_rw [mul_pow]
        rw [integral_const_mul, hscale, hV]
    _ ≤ K ^ (-s) * (K ^ s * σ + C * K ^ (max (2 * s - 1) (2 * α) + ε)) :=
      mul_le_mul_of_nonneg_left (by linarith [(le_abs_self
        ((variance μ H (hH.integrable one_le_two)).toReal - K ^ s * σ))]) (by positivity)
    _ = _ := by rw [mul_add, ← mul_assoc, hmain, one_mul]; rw [mul_left_comm, hpow]

/-- Halving the two variance-error exponents gives exactly the exponent
in equation (6.2). -/
lemma smoothing_error_exponent (s α τ : ℝ) :
    max (s - 1) (2 * α - s) + 2 * τ =
      2 * (max ((s - 1) / 2) (α - s / 2) + τ) := by
  rw [mul_add, mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  congr 1 <;> ring

end Riesz1.Internal
