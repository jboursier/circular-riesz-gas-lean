/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.CauchySchwarzIntegral
public import Mathlib.InformationTheory.KullbackLeibler.KLFun
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Elementary core of Pinsker's inequality

For a density `f ≥ 0` with `∫ f = 1` against a probability measure `ν`, the total variation
integral `∫ |1 - f|` is controlled by the relative entropy `∫ klFun ∘ f`. The proof is elementary
and uses the square-root substitution `s = √f`:

* pointwise, `(s - 1)² ≤ klFun (s²)`, since `x log x ≥ x - 1` for `x > 0`.
* pointwise, `|1 - f| = |s - 1| (s + 1)` and `(s + 1)² ≤ 2 f + 2`.
* the Cauchy–Schwarz inequality for `|s - 1|` and `s + 1` in `L²(ν)` then gives
  `(∫ |1 - f|)² ≤ (∫ (s - 1)²) (∫ (s + 1)²) ≤ 4 ∫ klFun ∘ f`.

The main result is `Riesz1.integral_abs_one_sub_sq_le`. It is the analytic input of the proof of
Pinsker's inequality `Riesz1.External.Pinsker`.
-/

@[expose] public section

open MeasureTheory InformationTheory

namespace Riesz1

/-- For `s ≥ 0`, `(s - 1)² ≤ klFun (s²)`. -/
lemma sq_sub_one_le_klFun_sq {s : ℝ} (hs : 0 ≤ s) :
    (s - 1) ^ 2 ≤ klFun (s ^ 2) := by
  rcases hs.eq_or_lt with rfl | hpos
  · simp [klFun_apply]
  · have h1 : s - 1 ≤ s * Real.log s := by
      have h2 := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hpos) hpos.le
      rwa [mul_sub, mul_one, mul_inv_cancel₀ hpos.ne'] at h2
    rw [klFun_apply, Real.log_pow]
    push_cast
    nlinarith [mul_nonneg hs (sub_nonneg.2 h1)]

/-- For `x ≥ 0`, `(√x - 1)² ≤ klFun x`. -/
lemma sq_sqrt_sub_one_le_klFun {x : ℝ} (hx : 0 ≤ x) :
    (√x - 1) ^ 2 ≤ klFun x := by
  have h := sq_sub_one_le_klFun_sq (Real.sqrt_nonneg x)
  rwa [Real.sq_sqrt hx] at h

/-- For `x ≥ 0`, `|1 - x| = |√x - 1| (√x + 1)`. -/
lemma abs_one_sub_eq_abs_sqrt_sub_one_mul {x : ℝ} (hx : 0 ≤ x) :
    |1 - x| = |√x - 1| * (√x + 1) := by
  have h : 1 - x = -((√x - 1) * (√x + 1)) := by
    linear_combination Real.sq_sqrt hx
  rw [h, abs_neg, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ √x + 1)]

/-- For `x ≥ 0`, `(√x + 1)² ≤ 2 x + 2`. -/
lemma sq_sqrt_add_one_le {x : ℝ} (hx : 0 ≤ x) :
    (√x + 1) ^ 2 ≤ 2 * x + 2 := by
  nlinarith [sq_nonneg (√x - 1), Real.sq_sqrt hx]

/-- The analytic core of Pinsker's inequality. Let `ν` be a probability measure and let
`f : Ω → ℝ` be a measurable nonnegative function with `∫ f dν = 1` such that `klFun ∘ f` is
integrable. Then `(∫ |1 - f| dν)² ≤ 4 ∫ klFun ∘ f dν`. -/
theorem integral_abs_one_sub_sq_le {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    [IsProbabilityMeasure ν] {f : Ω → ℝ} (hf_meas : Measurable f) (hf_nonneg : ∀ x, 0 ≤ f x)
    (hf_int : Integrable f ν) (hf_one : ∫ x, f x ∂ν = 1)
    (hk_int : Integrable (fun x => klFun (f x)) ν) :
    (∫ x, |1 - f x| ∂ν) ^ 2 ≤ 4 * ∫ x, klFun (f x) ∂ν := by
  have hs_meas : Measurable fun x => √(f x) := Real.continuous_sqrt.measurable.comp hf_meas
  have hX_meas : AEStronglyMeasurable (fun x => |√(f x) - 1|) ν :=
    (continuous_abs.measurable.comp (hs_meas.sub_const 1)).aestronglyMeasurable
  have hY_meas : AEStronglyMeasurable (fun x => √(f x) + 1) ν :=
    (hs_meas.add_const 1).aestronglyMeasurable
  -- Integrability of the squares `(√f - 1)²` and `(√f + 1)²`.
  have hX2_int : Integrable (fun x => |√(f x) - 1| ^ 2) ν := by
    refine hk_int.mono' ((hX_meas.pow 2)) (ae_of_all _ fun x => ?_)
    rw [sq_abs, Real.norm_of_nonneg (sq_nonneg _)]
    exact sq_sqrt_sub_one_le_klFun (hf_nonneg x)
  have hBound_int : Integrable (fun x => 2 * f x + 2) ν :=
    (hf_int.const_mul 2).add (integrable_const 2)
  have hY2_int : Integrable (fun x => (√(f x) + 1) ^ 2) ν := by
    refine hBound_int.mono' (hY_meas.pow 2) (ae_of_all _ fun x => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact sq_sqrt_add_one_le (hf_nonneg x)
  have hX : MemLp (fun x => |√(f x) - 1|) 2 ν :=
    (memLp_two_iff_integrable_sq hX_meas).2 hX2_int
  have hY : MemLp (fun x => √(f x) + 1) 2 ν :=
    (memLp_two_iff_integrable_sq hY_meas).2 hY2_int
  -- Rewrite the total variation integrand as a product, then apply Cauchy–Schwarz.
  have hTeq : ∫ x, |1 - f x| ∂ν = ∫ x, |√(f x) - 1| * (√(f x) + 1) ∂ν :=
    integral_congr_ae (ae_of_all _ fun x => abs_one_sub_eq_abs_sqrt_sub_one_mul (hf_nonneg x))
  have hCS := Riesz1.abs_integral_mul_le_sqrt_integral_sq hX hY
  have hT0 : 0 ≤ ∫ x, |1 - f x| ∂ν := integral_nonneg fun x => abs_nonneg _
  have hTle : ∫ x, |1 - f x| ∂ν ≤
      Real.sqrt (∫ x, |√(f x) - 1| ^ 2 ∂ν) * Real.sqrt (∫ x, (√(f x) + 1) ^ 2 ∂ν) := by
    rw [hTeq]
    exact (le_abs_self _).trans hCS
  have hP0 : 0 ≤ ∫ x, |√(f x) - 1| ^ 2 ∂ν := integral_nonneg fun x => sq_nonneg _
  have hQ0 : 0 ≤ ∫ x, (√(f x) + 1) ^ 2 ∂ν := integral_nonneg fun x => sq_nonneg _
  have hK0 : 0 ≤ ∫ x, klFun (f x) ∂ν :=
    integral_nonneg fun x => klFun_nonneg (hf_nonneg x)
  have hTsq : (∫ x, |1 - f x| ∂ν) ^ 2 ≤
      (∫ x, |√(f x) - 1| ^ 2 ∂ν) * ∫ x, (√(f x) + 1) ^ 2 ∂ν := by
    calc (∫ x, |1 - f x| ∂ν) ^ 2
        ≤ (Real.sqrt (∫ x, |√(f x) - 1| ^ 2 ∂ν) * Real.sqrt (∫ x, (√(f x) + 1) ^ 2 ∂ν)) ^ 2 :=
          pow_le_pow_left₀ hT0 hTle 2
      _ = (∫ x, |√(f x) - 1| ^ 2 ∂ν) * ∫ x, (√(f x) + 1) ^ 2 ∂ν := by
          rw [mul_pow, Real.sq_sqrt hP0, Real.sq_sqrt hQ0]
  -- Bound the two factors: `∫ (√f - 1)² ≤ ∫ klFun ∘ f` and `∫ (√f + 1)² ≤ 4`.
  have hPle : ∫ x, |√(f x) - 1| ^ 2 ∂ν ≤ ∫ x, klFun (f x) ∂ν :=
    integral_mono hX2_int hk_int fun x => by
      rw [sq_abs]
      exact sq_sqrt_sub_one_le_klFun (hf_nonneg x)
  have hQle : ∫ x, (√(f x) + 1) ^ 2 ∂ν ≤ 4 := by
    calc ∫ x, (√(f x) + 1) ^ 2 ∂ν ≤ ∫ x, (2 * f x + 2) ∂ν :=
          integral_mono hY2_int hBound_int fun x => sq_sqrt_add_one_le (hf_nonneg x)
      _ = 4 := by
          rw [integral_add (hf_int.const_mul 2) (integrable_const 2), integral_const_mul, hf_one]
          simp
          norm_num
  nlinarith [mul_nonneg (sub_nonneg.2 hPle) hQ0, mul_nonneg (sub_nonneg.2 hQle) hK0]

end Riesz1

end
