/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.VarianceFrozenIntegral
public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Covariance with a bounded variable

The covariance of a variable bounded in absolute value by `M` and a
square-integrable variable is at most `M` times its standard deviation.
The standard deviation uses the extended-valued variance. Its
finiteness is proved before applying `toReal`.
-/

public section

open MeasureTheory

namespace Riesz1

/-- Subtracting a constant preserves the variance on a probability
space. First-moment validity is explicit on both sides. -/
theorem frozenVariance_sub_const {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {F : Ω → ℝ}
    (hF : Integrable F μ) (c : ℝ) :
    variance μ (fun x => F x - c) (hF.sub (integrable_const c)) = variance μ F hF := by
  unfold variance
  rw [integral_sub hF (integrable_const c)]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, sub_sub_sub_cancel_right]

/-- Cauchy--Schwarz with the constant one on a probability space. -/
theorem boundedCov_integral_abs_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {F : Ω → ℝ} (hF : MemLp F 2 μ) :
    ∫ x, |F x| ∂μ ≤ Real.sqrt (∫ x, F x ^ 2 ∂μ) := by
  have htwo : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have h := integral_mul_norm_le_Lp_mul_Lq hpq
    (htwo.symm ▸ hF) (htwo.symm ▸ (memLp_const (1 : ℝ) : MemLp (fun _ : Ω => (1 : ℝ)) 2 μ))
  simpa only [Real.norm_eq_abs, abs_one, mul_one, Real.rpow_two, sq_abs, one_pow,
    integral_const, probReal_univ, smul_eq_mul, one_mul, Real.one_rpow,
    ← Real.sqrt_eq_rpow, Real.sqrt_one, mul_one] using h

/-- The covariance bound used in the last step of Theorem 3.
No centering assumption on either variable is needed. -/
theorem abs_covariance_le_bound_sqrt_variance {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {F G : Ω → ℝ}
    (hF : AEStronglyMeasurable F μ) (hG : MemLp G 2 μ) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ᵐ x ∂μ, |F x| ≤ M) :
    variance μ G (hG.integrable one_le_two) < ⊤ ∧
      |ProbabilityTheory.covariance F G μ| ≤
        M * Real.sqrt (variance μ G (hG.integrable one_le_two)).toReal := by
  have hF2 : MemLp F 2 μ := MemLp.of_bound hF M (by simpa only [Real.norm_eq_abs] using hbound)
  have hGi := hG.integrable one_le_two
  have hGc : MemLp (fun x => G x - ∫ y, G y ∂μ) 2 μ := hG.sub (memLp_const _)
  have hcenter : ProbabilityTheory.covariance F G μ = ∫ x, F x * (G x - ∫ y, G y ∂μ) ∂μ := by
    rw [ProbabilityTheory.covariance_eq_sub hF2 hG]
    simp_rw [mul_sub]
    change (∫ x, F x * G x ∂μ) - _ = _
    rw [integral_sub (show Integrable (fun x => F x * G x) μ from hF2.integrable_mul hG) (show Integrable (fun x => F x * ∫ y, G y ∂μ) μ from (hF2.integrable one_le_two).mul_const _),
      integral_mul_const]
  have hv := variance_eq_ofReal_integral_sq μ G hG
  refine ⟨hv ▸ ENNReal.ofReal_lt_top, ?_⟩
  rw [hv, ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _), hcenter]
  calc
    _ ≤ ∫ x, |F x * (G x - ∫ y, G y ∂μ)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, M * |G x - ∫ y, G y ∂μ| ∂μ := by
      apply integral_mono_ae (hF2.integrable_mul hGc).abs
        ((hGc.integrable one_le_two).abs.const_mul M)
      filter_upwards [hbound] with x hx
      simp only [Pi.mul_apply, abs_mul]
      exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
    _ = M * ∫ x, |G x - ∫ y, G y ∂μ| ∂μ := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (boundedCov_integral_abs_le hGc) hM

/-- The variance of a linear combination is bounded by the two
individual variances, with a constant independent of the variables. -/
theorem variance_const_mul_sub_le_two {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {F G : Ω → ℝ}
    (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) (β : ℝ) :
    variance μ (fun x => β * F x - G x)
        ((hF.const_mul β).sub hG |>.integrable one_le_two) ≤
      ENNReal.ofReal (2 * β ^ 2) * variance μ F (hF.integrable one_le_two) +
        2 * variance μ G (hG.integrable one_le_two) := by
  have hFi := hF.integrable one_le_two
  have hGi := hG.integrable one_le_two
  have hm : (∫ x, β * F x - G x ∂μ) = β * ∫ x, F x ∂μ - ∫ x, G x ∂μ := by
    rw [integral_sub (hFi.const_mul β) hGi, integral_const_mul]
  unfold variance
  rw [hm]
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (2 * β ^ 2) * ENNReal.ofReal ((F x - ∫ y, F y ∂μ) ^ 2) +
        2 * ENNReal.ofReal ((G x - ∫ y, G y ∂μ) ^ 2) ∂μ := by
      apply lintegral_mono
      intro x
      have h : (β * F x - G x - (β * ∫ y, F y ∂μ - ∫ y, G y ∂μ)) ^ 2 ≤
          (2 * β ^ 2) * (F x - ∫ y, F y ∂μ) ^ 2 + 2 * (G x - ∫ y, G y ∂μ) ^ 2 := by
        nlinarith [sq_nonneg (β * (F x - ∫ y, F y ∂μ) + (G x - ∫ y, G y ∂μ))]
      calc
        _ ≤ ENNReal.ofReal ((2 * β ^ 2) * (F x - ∫ y, F y ∂μ) ^ 2 +
            2 * (G x - ∫ y, G y ∂μ) ^ 2) := ENNReal.ofReal_le_ofReal h
        _ = _ := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          · exact ENNReal.ofReal_mul (by positivity)
          · rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
    _ = _ := by
      rw [lintegral_add_left' (((hFi.aemeasurable.sub_const _).pow_const 2).ennreal_ofReal.const_mul _),
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ (by norm_num)]

end Riesz1
