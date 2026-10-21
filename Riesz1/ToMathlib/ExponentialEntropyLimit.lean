/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.Herbst.Mgf
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# First variation of the weighted exponential comparison

The lemmas differentiate exponential moments of bounded continuous functions. They support
the Prékopa–Leindler proof of the Bakry–Émery criterion, following the first-variation
argument of Bobkov–Ledoux (2000), Proposition 3.1. All code in this module is original.
-/

public section

noncomputable section

open MeasureTheory Filter Topology Set

namespace Riesz1

variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
  {μ : Measure E}

/-- First variation of a bounded exponential perturbation of a finite measure. -/
theorem hasDerivAt_integral_exp_add [IsFiniteMeasure μ] {g h : E → ℝ}
    (hg : Continuous g) (hh : Continuous h) {K L : ℝ}
    (hK : ∀ x, |g x| ≤ K) (hL : ∀ x, |h x| ≤ L) :
    HasDerivAt (fun r : ℝ => ∫ x, Real.exp (g x + r * h x) ∂μ)
      (∫ x, Real.exp (g x) * h x ∂μ) 0 := by
  have hig : Integrable (fun x => Real.exp (g x)) μ := by
    simpa only [one_mul] using herbst_integrable_exp hg hK 1
  let μg := μ.withDensity (fun x => ENNReal.ofReal (Real.exp (g x)))
  let : IsFiniteMeasure μg := isFiniteMeasure_withDensity (by
    rw [← ofReal_integral_eq_lintegral_ofReal hig (ae_of_all _ fun _ => (Real.exp_pos _).le)]
    exact ENNReal.ofReal_ne_top)
  have hm := herbst_hasDerivAt_mgf (μ := μg) hh hL 0
  have heq (r : ℝ) : (∫ x, Real.exp (r * h x) ∂μg) =
      ∫ x, Real.exp (g x + r * h x) ∂μ := by
    dsimp only [μg]
    rw [integral_withDensity_eq_integral_toReal_smul (μ := μ)
      (f := fun x => ENNReal.ofReal (Real.exp (g x)))
      (ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp hg).measurable)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) (fun x => Real.exp (r * h x))]
    simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul, Real.exp_add]
  rw [show (fun r => ∫ x, Real.exp (r * h x) ∂μg) =
      (fun r => ∫ x, Real.exp (g x + r * h x) ∂μ) from funext heq] at hm
  simp only [zero_mul, Real.exp_zero, mul_one] at hm
  dsimp only [μg] at hm
  rw [integral_withDensity_eq_integral_toReal_smul (μ := μ)
      (f := fun x => ENNReal.ofReal (Real.exp (g x)))
    (ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp hg).measurable)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) h] at hm
  simpa only [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul] using hm

/-- First variation of the varying power of an exponential moment. -/
theorem hasDerivAt_power_integral_exp [IsProbabilityMeasure μ] {g : E → ℝ}
    (hg : Continuous g) {K : ℝ} (hK : ∀ x, |g x| ≤ K) :
    HasDerivAt (fun s : ℝ => (∫ x, Real.exp (g x / (1 - s)) ∂μ) ^ (1 - s))
      ((∫ x, g x * Real.exp (g x) ∂μ) -
        (∫ x, Real.exp (g x) ∂μ) * Real.log (∫ x, Real.exp (g x) ∂μ)) 0 := by
  have hr : HasDerivAt (fun s : ℝ => 1 / (1 - s)) 1 0 := by
    convert (hasDerivAt_const (0 : ℝ) (1 : ℝ)).div
      ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub (hasDerivAt_id 0)) (by norm_num) using 1
    · rfl
    · norm_num
  have hm := (herbst_hasDerivAt_mgf (μ := μ) hg hK (1 / (1 - 0))).comp 0 hr
  have hI : 0 < ∫ x, Real.exp (g x) ∂μ := by
    simpa only [one_mul] using herbst_integral_exp_pos (μ := μ) hg hK 1
  have hp := hm.rpow ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub (hasDerivAt_id 0))
    (by simpa using hI)
  convert hp using 1
  · ext s
    simp only [Function.comp_apply, Pi.sub_apply, id_eq]
    congr 1
    apply congrArg (fun f : E → ℝ => ∫ x, f x ∂μ)
    funext x
    congr 1
    ring
  · simp [sub_eq_add_neg]

/-- Differentiating a comparison valid immediately to the right of zero. -/
theorem deriv_le_of_eventually_le_right {f g : ℝ → ℝ} {a b : ℝ}
    (hf : HasDerivAt f a 0) (hg : HasDerivAt g b 0)
    (h0 : f 0 = g 0) (hle : ∀ᶠ s in 𝓝[>] (0 : ℝ), f s ≤ g s) : a ≤ b := by
  apply le_of_tendsto_of_tendsto hf.tendsto_slope_zero_right hg.tendsto_slope_zero_right
  filter_upwards [hle, self_mem_nhdsWithin] with s hs hs0
  simp only [zero_add, smul_eq_mul, h0]
  exact mul_le_mul_of_nonneg_left (sub_le_sub_right hs _) (inv_nonneg.mpr hs0.le)

/-- The scalar first-variation argument giving exponential entropy from a weighted comparison.
This is an internal implication. The comparison must be discharged at its application. -/
theorem exponential_entropy_le_of_comparison [IsProbabilityMeasure μ]
    {g h : E → ℝ} (hg : Continuous g) (hh : Continuous h) {K L κ M : ℝ}
    (hK : ∀ x, |g x| ≤ K) (hL : ∀ x, |h x| ≤ L) (hκ : 0 < κ)
    (hcomp : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      (∫ x, Real.exp (g x / (1 - s)) ∂μ) ^ (1 - s) ≤
        ∫ x, Real.exp (g x + s / (2 * (κ * (1 - s) - M * s)) * h x) ∂μ) :
    (∫ x, g x * Real.exp (g x) ∂μ) -
      (∫ x, Real.exp (g x) ∂μ) * Real.log (∫ x, Real.exp (g x) ∂μ) ≤
        (2 * κ)⁻¹ * ∫ x, Real.exp (g x) * h x ∂μ := by
  have ha : HasDerivAt (fun s : ℝ => s / (2 * (κ * (1 - s) - M * s)))
      ((2 * κ)⁻¹) 0 := by
    have hd := (hasDerivAt_id (0 : ℝ)).div
      (((hasDerivAt_const (0 : ℝ) (2 : ℝ)).mul
        (((hasDerivAt_const (0 : ℝ) κ).mul
          ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub (hasDerivAt_id 0))).sub
          ((hasDerivAt_const (0 : ℝ) M).mul (hasDerivAt_id 0)))))
      (by simpa using mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hκ.ne')
    convert hd using 1
    · rfl
    · simp only [Pi.mul_apply, Pi.sub_apply, id_eq, mul_zero, zero_mul, sub_zero,
        mul_one, one_mul]
      field_simp
  have hm : HasDerivAt (fun r : ℝ => ∫ x, Real.exp (g x + r * h x) ∂μ)
      (∫ x, Real.exp (g x) * h x ∂μ) (0 / (2 * (κ * (1 - 0) - M * 0))) := by
    simpa only [zero_div] using hasDerivAt_integral_exp_add (μ := μ) hg hh hK hL
  have hright := hm.comp 0 ha
  have hr : HasDerivAt
      (fun s : ℝ => ∫ x, Real.exp (g x + s / (2 * (κ * (1 - s) - M * s)) * h x) ∂μ)
      ((2 * κ)⁻¹ * ∫ x, Real.exp (g x) * h x ∂μ) 0 := by
    simpa only [Function.comp_def, zero_mul, sub_zero, mul_one, zero_div, mul_comm] using hright
  exact deriv_le_of_eventually_le_right (hasDerivAt_power_integral_exp hg hK) hr
    (by simp) hcomp

end Riesz1

end
