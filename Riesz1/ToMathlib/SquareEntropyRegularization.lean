/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.LogSobolevTransfer
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Positive regularization of square-test entropy

The smooth function `log(q² + ε)` connects exponential entropy to square-test entropy.
The regularized gradient energy is bounded by four times the original gradient energy.
This includes tests with zeros and supports the proof of the Bakry–Émery criterion.
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Riesz1

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsProbabilityMeasure μ]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The derivative of the logarithmic regularization, with its coefficient explicit. -/
theorem fderiv_log_square_add {q : E → ℝ} (hq : Differentiable ℝ q) {ε : ℝ} (hε : 0 < ε)
    (x : E) :
    fderiv ℝ (fun y => Real.log (q y ^ 2 + ε)) x =
      ((q x ^ 2 + ε)⁻¹ * (2 * q x)) • fderiv ℝ q x := by
  have hd := (((hq x).hasFDerivAt.pow 2).add_const ε).log
    (ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) hε))
  simpa only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, smul_smul, nsmul_eq_mul] using hd.fderiv

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The regularized logarithmic gradient energy is bounded by the square-test energy. -/
theorem exp_log_square_mul_fderiv_sq_le {q : E → ℝ} (hq : Differentiable ℝ q)
    {ε : ℝ} (hε : 0 < ε) (x : E) :
    Real.exp (Real.log (q x ^ 2 + ε)) *
      ‖fderiv ℝ (fun y => Real.log (q y ^ 2 + ε)) x‖ ^ 2 ≤
        4 * ‖fderiv ℝ q x‖ ^ 2 := by
  have hp : 0 < q x ^ 2 + ε := add_pos_of_nonneg_of_pos (sq_nonneg _) hε
  rw [Real.exp_log hp, fderiv_log_square_add hq hε, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]
  have he : (q x ^ 2 + ε) * ((q x ^ 2 + ε)⁻¹ * (2 * q x)) ^ 2 * ‖fderiv ℝ q x‖ ^ 2 =
      4 * (q x ^ 2 / (q x ^ 2 + ε)) * ‖fderiv ℝ q x‖ ^ 2 := by
    field_simp
    ring
  rw [← mul_assoc, he]
  have hr : q x ^ 2 / (q x ^ 2 + ε) ≤ 1 := (div_le_one hp).mpr (by linarith)
  nlinarith [mul_le_mul_of_nonneg_right hr (sq_nonneg ‖fderiv ℝ q x‖)]

omit [FiniteDimensional ℝ E] in
/-- A regularized square has the sharp entropy bound whenever bounded exponential tests do.
The premise is an internal implication to be discharged by its caller. -/
theorem square_entropy_regularized_of_exponential (c : ℝ) (hc : 0 ≤ c)
    (hExp : ∀ g : E → ℝ, ContDiff ℝ ∞ g → (∃ K, ∀ x, |g x| ≤ K) →
      (∃ D, ∀ x, ‖fderiv ℝ g x‖ ≤ D) →
      (∫ x, g x * Real.exp (g x) ∂μ) -
        (∫ x, Real.exp (g x) ∂μ) * Real.log (∫ x, Real.exp (g x) ∂μ) ≤
          c * ∫ x, Real.exp (g x) * ‖fderiv ℝ g x‖ ^ 2 ∂μ)
    {q : E → ℝ} (hq : ContDiff ℝ ∞ q) {K D : ℝ}
    (hK : ∀ x, |q x| ≤ K) (hD : ∀ x, ‖fderiv ℝ q x‖ ≤ D)
    {ε : ℝ} (hε : 0 < ε) :
    -(∫ x, Real.negMulLog (q x ^ 2 + ε) ∂μ) +
      Real.negMulLog (∫ x, q x ^ 2 + ε ∂μ) ≤
        4 * c * ∫ x, ‖fderiv ℝ q x‖ ^ 2 ∂μ := by
  let g := fun x => Real.log (q x ^ 2 + ε)
  have hp (x : E) : 0 < q x ^ 2 + ε := add_pos_of_nonneg_of_pos (sq_nonneg _) hε
  have hg : ContDiff ℝ ∞ g := (hq.pow 2 |>.add contDiff_const).log (fun x => (hp x).ne')
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0)
  have hs (x : E) : q x ^ 2 ≤ K ^ 2 := by
    nlinarith [sq_abs (q x), mul_self_le_mul_self (abs_nonneg (q x)) (hK x)]
  have hbg : ∃ C, ∀ x, |g x| ≤ C := by
    refine ⟨|Real.log ε| + |Real.log (K ^ 2 + ε)|, fun x => ?_⟩
    have hl := Real.log_le_log hε (show ε ≤ q x ^ 2 + ε by linarith [sq_nonneg (q x)])
    have hu := Real.log_le_log (hp x) (show q x ^ 2 + ε ≤ K ^ 2 + ε by linarith [hs x])
    change |Real.log (q x ^ 2 + ε)| ≤ _
    rw [abs_le]
    constructor <;> linarith [le_abs_self (Real.log ε), neg_abs_le (Real.log ε),
      le_abs_self (Real.log (K ^ 2 + ε)), abs_nonneg (Real.log ε),
      abs_nonneg (Real.log (K ^ 2 + ε))]
  have hbD : ∃ C, ∀ x, ‖fderiv ℝ g x‖ ≤ C := by
    refine ⟨(ε⁻¹ * (2 * K)) * D, fun x => ?_⟩
    rw [fderiv_log_square_add (hq.differentiable (by simp)) hε, norm_smul,
      Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.mpr (hp x)), abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hi : (q x ^ 2 + ε)⁻¹ ≤ ε⁻¹ := inv_anti₀ hε (by linarith [sq_nonneg (q x)])
    have hcoeff : (q x ^ 2 + ε)⁻¹ * (2 * |q x|) ≤ ε⁻¹ * (2 * K) :=
      mul_le_mul hi (mul_le_mul_of_nonneg_left (hK x) (by norm_num))
        (by positivity) (by positivity)
    exact mul_le_mul hcoeff (hD x) (norm_nonneg _) (by positivity)
  have hi := hExp g hg hbg hbD
  have henergy := (LogSobolevInternal.test_integrable (μ := μ)
    (hq.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)) hK hD).2.2
  have hleft : Integrable (fun x => Real.exp (g x) * ‖fderiv ℝ g x‖ ^ 2) μ := by
    apply (henergy.const_mul 4).mono'
      (((Real.continuous_exp.comp hg.continuous).mul
        ((hg.continuous_fderiv (by simp)).norm.pow 2)).aestronglyMeasurable)
    filter_upwards with x
    change ‖Real.exp (g x) * ‖fderiv ℝ g x‖ ^ 2‖ ≤ 4 * ‖fderiv ℝ q x‖ ^ 2
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
    exact exp_log_square_mul_fderiv_sq_le (hq.differentiable (by simp)) hε x
  have he := integral_mono hleft (henergy.const_mul 4)
    (fun x => exp_log_square_mul_fderiv_sq_le (hq.differentiable (by simp)) hε x)
  rw [integral_const_mul] at he
  have hi' := hi.trans (mul_le_mul_of_nonneg_left he hc)
  have hexp (x : E) : Real.exp (g x) = q x ^ 2 + ε := Real.exp_log (hp x)
  simp_rw [hexp] at hi'
  have hfun : (fun x => g x * (q x ^ 2 + ε)) = fun x => -Real.negMulLog (q x ^ 2 + ε) := by
    funext x
    simp only [g, Real.negMulLog_def]
    ring
  rw [hfun, integral_neg] at hi'
  have hec : c * (4 * ∫ x, ‖fderiv ℝ q x‖ ^ 2 ∂μ) =
      4 * c * ∫ x, ‖fderiv ℝ q x‖ ^ 2 ∂μ := by ring
  rw [hec] at hi'
  simpa only [Real.negMulLog_def, sub_eq_add_neg, neg_mul] using hi'

omit [FiniteDimensional ℝ E] in
/-- Exponential-test entropy implies the square-test inequality, including zeros. -/
theorem square_entropy_of_exponential (c : ℝ) (hc : 0 ≤ c)
    (hExp : ∀ g : E → ℝ, ContDiff ℝ ∞ g → (∃ K, ∀ x, |g x| ≤ K) →
      (∃ D, ∀ x, ‖fderiv ℝ g x‖ ≤ D) →
      (∫ x, g x * Real.exp (g x) ∂μ) -
        (∫ x, Real.exp (g x) ∂μ) * Real.log (∫ x, Real.exp (g x) ∂μ) ≤
          c * ∫ x, Real.exp (g x) * ‖fderiv ℝ g x‖ ^ 2 ∂μ)
    {q : E → ℝ} (hq : ContDiff ℝ ∞ q) {K D : ℝ}
    (hK : ∀ x, |q x| ≤ K) (hD : ∀ x, ‖fderiv ℝ q x‖ ≤ D) :
    -(∫ x, Real.negMulLog (q x ^ 2) ∂μ) + Real.negMulLog (∫ x, q x ^ 2 ∂μ) ≤
      4 * c * ∫ x, ‖fderiv ℝ q x‖ ^ 2 ∂μ := by
  let ε (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hε (n) : 0 < ε n := by dsimp [ε]; positivity
  have hε1 (n) : ε n ≤ 1 := by
    dsimp [ε]
    apply (div_le_one (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have htε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hs (x : E) : q x ^ 2 ≤ K ^ 2 := by
    nlinarith [sq_abs (q x), mul_self_le_mul_self (abs_nonneg (q x)) (hK x)]
  have hbound (n) (x : E) : |q x ^ 2 + ε n| ≤ K ^ 2 + 1 := by
    rw [abs_of_nonneg (by positivity)]
    linarith [hs x, hε1 n]
  have ht (x : E) : Tendsto (fun n => q x ^ 2 + ε n) atTop (𝓝 (q x ^ 2)) := by
    simpa only [add_zero] using tendsto_const_nhds.add htε
  have ht₁ := LogSobolevInternal.tendsto_integral_comp (μ := μ)
    (fun n => (hq.continuous.pow 2).add continuous_const) hbound ht Real.continuous_negMulLog
  have ht₂ := LogSobolevInternal.tendsto_integral_comp (μ := μ)
    (fun n => (hq.continuous.pow 2).add continuous_const) hbound ht continuous_id
  exact le_of_tendsto (ht₁.neg.add (Real.continuous_negMulLog.tendsto _ |>.comp ht₂))
    (Eventually.of_forall fun n => square_entropy_regularized_of_exponential c hc hExp hq hK hD (hε n))

end Riesz1

end
