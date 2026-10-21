/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Heat kernel on the circle

For a time `t > 0` the heat kernel on the circle `ℝ / ℤ` is the periodic function
`W_t(x) = ∑_{k ∈ ℤ} exp(-4π²k²t) cos(2πkx)`, the real form of the series
`∑_{k ∈ ℤ} exp(-4π²k²t) e^{2πikx}`. See Lemma 2.1.

The definition takes the time together with the proof `0 < t`, so that the kernel is defined on
its whole carrier and carries no junk value at `t ≤ 0`, where the series diverges. The value does
not depend on the proof.

Main results:
* `circleHeatKernel_eq_gauss`: the periodized Gaussian formula (equation (2.7)).
* `circleHeatKernel_pos`, `circleHeatKernel_periodic`, `continuous_circleHeatKernel`:
  positivity, period `1` and continuity in the space variable.
* `intervalIntegral_circleHeatKernel`: the kernel has mass one on `[0, 1]`.

The proofs pass through the Jacobi theta series `jacobiTheta₂_term` at `τ = 4πt i`, and through
Mathlib's Poisson summation formula `Complex.tsum_exp_neg_quadratic` for the Gaussian.
-/

public section

open MeasureTheory Set intervalIntegral
open scoped Real

namespace Riesz1

open Complex (I)

/-- The heat kernel on the circle `ℝ / ℤ` at time `t > 0`, in real form. The argument `_ht` only
records the domain of the time. The value is the series itself. -/
noncomputable def circleHeatKernel (t : ℝ) (_ht : 0 < t) (x : ℝ) : ℝ :=
  ∑' k : ℤ, Real.exp (-4 * π ^ 2 * (k : ℝ) ^ 2 * t) * Real.cos (2 * π * k * x)

/-- The complex Jacobi summand at `τ = 4πt i` is the Gaussian times the character `e^{2πinx}`. -/
lemma jacobiTheta₂_term_heat_eq (t : ℝ) (n : ℤ) (x : ℝ) :
    jacobiTheta₂_term n x (4 * π * t * I) =
      Complex.exp ((-4 * π ^ 2 * (n : ℝ) ^ 2 * t : ℝ) : ℂ) *
        Complex.exp ((2 * π * (n : ℝ) * x : ℝ) * I) := by
  rw [← Complex.exp_add, jacobiTheta₂_term]
  congr 1
  push_cast
  linear_combination (4 * (π : ℂ) ^ 2 * (n : ℂ) ^ 2 * (t : ℂ)) * Complex.I_sq

/-- The real part of the complex Jacobi summand is the real summand of the heat kernel. -/
lemma re_jacobiTheta₂_term_heat (t : ℝ) (n : ℤ) (x : ℝ) :
    (jacobiTheta₂_term n x (4 * π * t * I)).re =
      Real.exp (-4 * π ^ 2 * (n : ℝ) ^ 2 * t) * Real.cos (2 * π * (n : ℝ) * x) := by
  rw [jacobiTheta₂_term_heat_eq, ← Complex.ofReal_exp, Complex.re_ofReal_mul,
    Complex.exp_ofReal_mul_I_re]

/-- The Jacobi series at `τ = 4πt i` is summable for `t > 0`. -/
lemma summable_jacobiTheta₂_term_heat {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Summable (fun n : ℤ => jacobiTheta₂_term n x (4 * π * t * I)) := by
  rw [summable_jacobiTheta₂_term_iff]
  simp
  positivity

/-- The Gaussian weights `exp(-4π²n²t)` are summable over `ℤ` for `t > 0`. -/
lemma summable_exp_neg_mul_sq (t : ℝ) (ht : 0 < t) :
    Summable (fun n : ℤ => Real.exp (-4 * π ^ 2 * (n : ℝ) ^ 2 * t)) := by
  refine (Complex.hasSum_re (summable_jacobiTheta₂_term_heat ht 0).hasSum).summable.congr
    fun n => ?_
  rw [re_jacobiTheta₂_term_heat t n 0]
  simp

/-- The summands of the heat kernel are summable for `t > 0`, for every `x`. -/
lemma summable_circleHeatKernel_terms {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Summable (fun k : ℤ => Real.exp (-4 * π ^ 2 * (k : ℝ) ^ 2 * t) * Real.cos (2 * π * k * x)) :=
  Summable.of_norm_bounded (summable_exp_neg_mul_sq t ht) fun k => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)

/-- The heat kernel is the real part of the Jacobi series at `τ = 4πt i`. -/
lemma circleHeatKernel_eq_re_tsum (t : ℝ) (ht : 0 < t) (x : ℝ) :
    circleHeatKernel t ht x = (∑' n : ℤ, jacobiTheta₂_term n x (4 * π * t * I)).re := by
  rw [Complex.re_tsum (summable_jacobiTheta₂_term_heat ht x)]
  exact tsum_congr fun n => (re_jacobiTheta₂_term_heat t n x).symm

/-- The imaginary part of the complex Jacobi summand is `exp(-4π²n²t) sin(2πnx)`. -/
lemma im_jacobiTheta₂_term_heat (t : ℝ) (n : ℤ) (x : ℝ) :
    (jacobiTheta₂_term n x (4 * π * t * I)).im =
      Real.exp (-4 * π ^ 2 * (n : ℝ) ^ 2 * t) * Real.sin (2 * π * (n : ℝ) * x) := by
  rw [jacobiTheta₂_term_heat_eq, ← Complex.ofReal_exp, Complex.im_ofReal_mul,
    Complex.exp_ofReal_mul_I_im]

/-- The imaginary parts of the Jacobi series cancel under `k ↦ -k`, so their sum is zero. -/
lemma tsum_im_jacobiTheta₂_term_heat_eq_zero (t : ℝ) (x : ℝ) :
    ∑' k : ℤ, (jacobiTheta₂_term k x (4 * π * t * I)).im = 0 := by
  have hodd : ∀ k : ℤ, (jacobiTheta₂_term (-k) x (4 * π * t * I)).im =
      -(jacobiTheta₂_term k x (4 * π * t * I)).im := by
    intro k
    rw [im_jacobiTheta₂_term_heat, im_jacobiTheta₂_term_heat]
    have e1 : (-4 * π ^ 2 * ((-k : ℤ) : ℝ) ^ 2 * t) = -4 * π ^ 2 * (k : ℝ) ^ 2 * t := by
      push_cast
      ring
    have e2 : 2 * π * ((-k : ℤ) : ℝ) * x = -(2 * π * (k : ℝ) * x) := by
      push_cast
      ring
    rw [e1, e2, Real.sin_neg]
    ring
  have h : ∑' k : ℤ, (jacobiTheta₂_term (-k) x (4 * π * t * I)).im =
      ∑' k : ℤ, (jacobiTheta₂_term k x (4 * π * t * I)).im :=
    (Equiv.neg ℤ).tsum_eq (fun k => (jacobiTheta₂_term k x (4 * π * t * I)).im)
  rw [tsum_congr hodd, tsum_neg] at h
  linarith

/-- The heat kernel equals the complex series `∑_k exp(-4π²k²t) e^{2πikx}` for `t > 0`, whose
imaginary part vanishes. -/
theorem circleHeatKernel_eq_complex_tsum (t : ℝ) (ht : 0 < t) (x : ℝ) :
    ∑' k : ℤ, Complex.exp ((-4 * π ^ 2 * (k : ℝ) ^ 2 * t : ℝ) : ℂ) *
      Complex.exp ((2 * π * (k : ℝ) * x : ℝ) * I) = (circleHeatKernel t ht x : ℂ) := by
  simp only [← jacobiTheta₂_term_heat_eq]
  refine Complex.ext ?_ ?_
  · rw [Complex.ofReal_re, circleHeatKernel_eq_re_tsum t ht x]
  · rw [Complex.ofReal_im, ← (Complex.hasSum_im (summable_jacobiTheta₂_term_heat ht x).hasSum).tsum_eq,
      tsum_im_jacobiTheta₂_term_heat_eq_zero]

/-- The periodized Gaussian formula for the heat kernel, equation (2.7):
`W_t(x) = (4πt)^{-1/2} ∑_{n ∈ ℤ} exp(-(x - n)² / (4t))`. -/
theorem circleHeatKernel_eq_gauss (t : ℝ) (ht : 0 < t) (x : ℝ) :
    circleHeatKernel t ht x =
      (4 * π * t) ^ (-(1 / 2 : ℝ)) * ∑' n : ℤ, Real.exp (-(x - n) ^ 2 / (4 * t)) := by
  have h4 : 0 < 4 * π * t := by positivity
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have ha : 0 < (((4 * π * t : ℝ) : ℂ)).re := by rw [Complex.ofReal_re]; exact h4
  -- The Jacobi summand, rewritten with the Poisson parameters `a = 4πt` and `b = i x`.
  have hL : (∑' n : ℤ, jacobiTheta₂_term n x (4 * π * t * I)) =
      ∑' n : ℤ, Complex.exp (-π * ((4 * π * t : ℝ) : ℂ) * (n : ℂ) ^ 2 +
        2 * π * (I * x) * (n : ℂ)) := by
    refine tsum_congr fun n => ?_
    rw [jacobiTheta₂_term]
    congr 1
    push_cast
    linear_combination (4 * (π : ℂ) ^ 2 * (n : ℂ) ^ 2 * (t : ℂ)) * Complex.I_sq
  -- Each Poisson summand is a real Gaussian, since `(n + i (i x))² = (n - x)²`.
  have hR : ∀ n : ℤ, Complex.exp (-π / ((4 * π * t : ℝ) : ℂ) *
      ((n : ℂ) + I * (I * x)) ^ 2) = ((Real.exp (-(x - n) ^ 2 / (4 * t)) : ℝ) : ℂ) := by
    intro n
    rw [Complex.ofReal_exp]
    congr 1
    have hn : (n : ℂ) + I * (I * x) = ((n - x : ℝ) : ℂ) := by
      push_cast
      linear_combination (x : ℂ) * Complex.I_sq
    rw [hn]
    push_cast
    field_simp
    ring
  have hS : (∑' n : ℤ, Complex.exp (-π / ((4 * π * t : ℝ) : ℂ) *
      ((n : ℂ) + I * (I * x)) ^ 2)) =
        ((∑' n : ℤ, Real.exp (-(x - n) ^ 2 / (4 * t)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    exact tsum_congr hR
  -- The square root of `a = 4πt` in the Poisson formula is the real power `(4πt)^{1/2}`.
  have hpow : (1 : ℂ) / ((4 * π * t : ℝ) : ℂ) ^ (1 / 2 : ℂ) =
      (((4 * π * t) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
    have e : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
    rw [e, ← Complex.ofReal_cpow h4.le, Real.rpow_neg h4.le, Complex.ofReal_inv, one_div]
  have key := Complex.tsum_exp_neg_quadratic ha (I * x)
  have hcomb : (∑' n : ℤ, jacobiTheta₂_term n x (4 * π * t * I)) =
      (((4 * π * t) ^ (-(1 / 2 : ℝ)) * ∑' n : ℤ, Real.exp (-(x - n) ^ 2 / (4 * t)) : ℝ) : ℂ) := by
    rw [hL, key, hS, hpow, Complex.ofReal_mul]
  rw [circleHeatKernel_eq_re_tsum t ht x, hcomb, Complex.ofReal_re]

/-- The Gaussian weights `exp(-(x - n)² / (4t))` are summable over `n ∈ ℤ` for `t > 0`. -/
lemma summable_gauss_int (t : ℝ) (ht : 0 < t) (x : ℝ) :
    Summable (fun n : ℤ => Real.exp (-(x - n) ^ 2 / (4 * t))) := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  set s : ℝ := 1 / (32 * π ^ 2 * t) with hs_def
  have hs : 0 < s := by positivity
  refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) (fun n => ?_)
    ((summable_exp_neg_mul_sq s hs).mul_left (Real.exp (x ^ 2 / (4 * t))))
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have e : -4 * π ^ 2 * (n : ℝ) ^ 2 * s = -(n : ℝ) ^ 2 / (8 * t) := by
    rw [hs_def]
    field_simp
    ring
  have ident : x ^ 2 / (4 * t) + -((n : ℝ) ^ 2 / (8 * t)) + (x - n) ^ 2 / (4 * t) =
      (2 * x - n) ^ 2 / (8 * t) := by
    field_simp
    ring
  have nonneg : 0 ≤ (2 * x - n) ^ 2 / (8 * t) := by positivity
  have h1 : -(x - n) ^ 2 / (4 * t) = -((x - n) ^ 2 / (4 * t)) := neg_div _ _
  have h2 : -(n : ℝ) ^ 2 / (8 * t) = -((n : ℝ) ^ 2 / (8 * t)) := neg_div _ _
  rw [e, h1, h2]
  linarith

/-- The heat kernel is positive, by equation (2.7). -/
theorem circleHeatKernel_pos (t : ℝ) (ht : 0 < t) (x : ℝ) : 0 < circleHeatKernel t ht x := by
  rw [circleHeatKernel_eq_gauss t ht x]
  exact mul_pos (Real.rpow_pos_of_pos (by positivity) _)
    ((summable_gauss_int t ht x).tsum_pos (fun n => (Real.exp_pos _).le) 0 (Real.exp_pos _))

/-- The heat kernel is periodic with period `1`. -/
theorem circleHeatKernel_periodic (t : ℝ) (ht : 0 < t) :
    Function.Periodic (circleHeatKernel t ht) 1 := by
  intro x
  unfold circleHeatKernel
  refine tsum_congr fun k => ?_
  congr 1
  have e : 2 * π * (k : ℝ) * (x + 1) = 2 * π * k * x + (k : ℝ) * (2 * π) := by ring
  rw [e, Real.cos_add_int_mul_two_pi]

/-- The heat kernel is continuous in the space variable. -/
theorem continuous_circleHeatKernel (t : ℝ) (ht : 0 < t) :
    Continuous (circleHeatKernel t ht) := by
  unfold circleHeatKernel
  refine continuous_tsum (fun k => ?_) (summable_exp_neg_mul_sq t ht) (fun k x => ?_)
  · fun_prop
  · rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)

/-- The Fourier modes `cos(2πkx)` have integral `0` over `[0, 1]` for `k ≠ 0`. -/
lemma intervalIntegral_cos_two_pi_mul_eq_zero {k : ℤ} (hk : k ≠ 0) :
    ∫ x in (0 : ℝ)..1, Real.cos (2 * π * k * x) = 0 := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hc : (2 * π * k : ℝ) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hk'
  rw [intervalIntegral.integral_comp_mul_left (fun y => Real.cos y) hc, integral_cos]
  have hsin : Real.sin (2 * π * k) = 0 := by
    have e : 2 * π * (k : ℝ) = ((2 * k : ℤ) : ℝ) * π := by push_cast; ring
    rw [e, Real.sin_int_mul_pi]
  simp [hsin]

/-- The heat kernel has mass one on the unit interval, equation (2.7) and the proof of
Lemma 2.1. -/
theorem intervalIntegral_circleHeatKernel (t : ℝ) (ht : 0 < t) :
    ∫ x in (0 : ℝ)..1, circleHeatKernel t ht x = 1 := by
  -- Each Fourier mode integrates to the Kronecker delta.
  have hmode : ∀ k : ℤ, ∫ x in (0 : ℝ)..1,
      Real.exp (-4 * π ^ 2 * (k : ℝ) ^ 2 * t) * Real.cos (2 * π * k * x) =
        if k = 0 then 1 else 0 := by
    intro k
    by_cases hk : k = 0
    · subst hk
      simp
    · rw [intervalIntegral.integral_const_mul, intervalIntegral_cos_two_pi_mul_eq_zero hk, mul_zero]
      simp [hk]
  -- Interchange the sum and the integral by dominated convergence, with bounds free of `x`.
  have hDC := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := 0) (b := 1)
    (F := fun (k : ℤ) (x : ℝ) => Real.exp (-4 * π ^ 2 * (k : ℝ) ^ 2 * t) * Real.cos (2 * π * k * x))
    (f := circleHeatKernel t ht)
    (bound := fun (k : ℤ) (_ : ℝ) => Real.exp (-4 * π ^ 2 * (k : ℝ) ^ 2 * t))
    (fun (k : ℤ) => Continuous.aestronglyMeasurable (by fun_prop))
    (fun k => Filter.Eventually.of_forall fun x _ => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _))
    (Filter.Eventually.of_forall fun _ _ => summable_exp_neg_mul_sq t ht)
    (intervalIntegrable_const)
    (Filter.Eventually.of_forall fun x _ => (summable_circleHeatKernel_terms ht x).hasSum)
  have hsingle : HasSum (fun k : ℤ => ∫ x in (0 : ℝ)..1,
      Real.exp (-4 * π ^ 2 * (k : ℝ) ^ 2 * t) * Real.cos (2 * π * k * x))
      (∫ x in (0 : ℝ)..1, Real.exp (-4 * π ^ 2 * ((0 : ℤ) : ℝ) ^ 2 * t) *
        Real.cos (2 * π * ((0 : ℤ) : ℝ) * x)) :=
    hasSum_single 0 fun k hk => by rw [hmode k]; simp [hk]
  have hval := hDC.unique hsingle
  rw [hval]
  simp

end Riesz1
