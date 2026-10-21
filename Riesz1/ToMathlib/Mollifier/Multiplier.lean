/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Tactic

/-!
# Fourier multiplier of a circle mollifier

A circle mollifier is an even, smooth, nonnegative function `ρ : ℝ → ℝ` supported in
`(-1/2, 1/2)` with unit integral. Its Fourier transform `ρ̂(t) = ∫ ρ(u) e^{-2πi t u} du`
(Mathlib's normalization) is real, lies in `[-1, 1]`, equals `1` at `t = 0`, and satisfies
`0 ≤ 1 - ρ̂(t) ≤ 8 min(t², 1)`. These bounds give the regularization multiplier estimates
of Lemma 5.1.

Main results:
* `mollifierFT_ofReal`: the transform is the real number `mollifierFT ρ t`.
* `mollifierFT_abs_le_one`, `mollifierFT_zero`: `|ρ̂| ≤ 1` and `ρ̂(0) = 1`.
* `mollifierFT_one_sub_nonneg`, `mollifierFT_one_sub_le`: `0 ≤ 1 - ρ̂(t) ≤ 8 min(t², 1)`.
* `mollifierFT_sq_one_sub_le`, `mollifierFT_sq_le_one`, `one_sub_mollifierFT_sq_le`: the squared
  forms used for Sobolev seminorms, with constant `16`.
* `min_sq_le_abs_rpow`: `min(t², 1) ≤ |t|^(2r)` for `0 < r ≤ 1`.
-/

public section

open MeasureTheory Real
open scoped ContDiff FourierTransform

namespace Riesz1

/-- A circle mollifier: an even, smooth, nonnegative function supported in `(-1/2, 1/2)` whose
integral is one. -/
@[expose] def IsCircleMollifier (ρ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ ρ ∧ Function.Even ρ ∧ (∀ x, 0 ≤ ρ x) ∧
    Function.support ρ ⊆ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ∧ ∫ x, ρ x = 1

/-- The real Fourier transform `ρ̂(t) = ∫ ρ(u) e^{-2πi t u} du` of a circle mollifier, taken as
the real part of Mathlib's Fourier transform `𝓕`. For an even `ρ` the imaginary part vanishes,
see `mollifierFT_ofReal`. -/
noncomputable def mollifierFT (ρ : ℝ → ℝ) (t : ℝ) : ℝ :=
  (𝓕 (fun u => (ρ u : ℂ)) t).re

variable {ρ : ℝ → ℝ}

lemma IsCircleMollifier.continuous (hρ : IsCircleMollifier ρ) : Continuous ρ :=
  hρ.1.continuous

lemma IsCircleMollifier.hasCompactSupport (hρ : IsCircleMollifier ρ) : HasCompactSupport ρ :=
  HasCompactSupport.intro (K := Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) isCompact_Icc fun _ hx =>
    Function.notMem_support.mp fun hmem => hx (Set.Ioo_subset_Icc_self (hρ.2.2.2.1 hmem))

lemma IsCircleMollifier.integrable (hρ : IsCircleMollifier ρ) : Integrable ρ :=
  hρ.continuous.integrable_of_hasCompactSupport hρ.hasCompactSupport

/-- Points where the mollifier does not vanish lie in `(-1/2, 1/2)`. -/
lemma IsCircleMollifier.abs_lt_of_ne_zero (hρ : IsCircleMollifier ρ) {u : ℝ} (hu : ρ u ≠ 0) :
    |u| < 1 / 2 :=
  abs_lt.mpr (hρ.2.2.2.1 (Function.mem_support.mpr hu))

/-- Multiplying the mollifier by a continuous bounded function gives an integrable function. -/
lemma IsCircleMollifier.integrable_mul (hρ : IsCircleMollifier ρ) {f : ℝ → ℝ} (hf : Continuous f)
    {c : ℝ} (hc : ∀ u, |f u| ≤ c) : Integrable (fun u => ρ u * f u) := by
  refine (hρ.integrable.bdd_mul hf.aestronglyMeasurable (c := c)
    (Filter.Eventually.of_forall fun u => ?_)).congr
    (Filter.Eventually.of_forall fun u => mul_comm _ _)
  rw [Real.norm_eq_abs]
  exact hc u

/-- The imaginary part of the transform integrates to zero, since `ρ` is even and the sine is
odd. -/
lemma IsCircleMollifier.integral_mul_sin (hρ : IsCircleMollifier ρ) (t : ℝ) :
    ∫ u, ρ u * Real.sin (2 * π * t * u) = 0 := by
  have h := Measure.integral_comp_mul_left (fun u => ρ u * Real.sin (2 * π * t * u)) (-1)
  have hodd : ∀ u, ρ (-u) * Real.sin (2 * π * t * (-u)) = -(ρ u * Real.sin (2 * π * t * u)) := by
    intro u
    rw [hρ.2.1 u, mul_neg, Real.sin_neg]
    ring
  simp only [neg_one_mul, inv_neg, inv_one, abs_neg, abs_one, one_smul, hodd, integral_neg]
    at h
  linarith

/-- The integrand of the Fourier transform of `ρ` at `t`, written with the exponential. -/
lemma IsCircleMollifier.integrable_fourier_integrand (hρ : IsCircleMollifier ρ) (t : ℝ) :
    Integrable (fun u : ℝ => Complex.exp (↑(-2 * π * u * t) * Complex.I) • (ρ u : ℂ)) := by
  have hc : Continuous fun u : ℝ => Complex.exp (↑(-2 * π * u * t) * Complex.I) := by
    fun_prop
  have hC : Integrable (fun u : ℝ => (ρ u : ℂ)) := hρ.integrable.ofReal
  have hb := hC.bdd_mul hc.aestronglyMeasurable (c := 1)
    (Filter.Eventually.of_forall fun u => (Complex.norm_exp_ofReal_mul_I _).le)
  simpa only [smul_eq_mul] using hb

/-- The real part of the transform is the integral of `ρ(u) cos(2π t u)`. -/
lemma mollifierFT_eq_integral_cos (hρ : IsCircleMollifier ρ) (t : ℝ) :
    mollifierFT ρ t = ∫ u, ρ u * Real.cos (2 * π * t * u) := by
  have key := integral_re (hρ.integrable_fourier_integrand t)
  simp only [RCLike.re_to_complex] at key
  unfold mollifierFT
  rw [fourier_real_eq_integral_exp_smul]
  rw [← key]
  congr 1
  ext u
  have harg : -2 * π * u * t = -(2 * π * t * u) := by ring
  simp only [smul_eq_mul, Complex.mul_re, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im, Complex.ofReal_re, Complex.ofReal_im, harg, Real.cos_neg]
  ring

/-- For an even mollifier the Fourier transform is real. -/
lemma mollifierFT_ofReal (hρ : IsCircleMollifier ρ) (t : ℝ) :
    𝓕 (fun u => (ρ u : ℂ)) t = (mollifierFT ρ t : ℂ) := by
  have him : (𝓕 (fun u => (ρ u : ℂ)) t).im = 0 := by
    have key := integral_im (hρ.integrable_fourier_integrand t)
    simp only [RCLike.im_to_complex] at key
    rw [fourier_real_eq_integral_exp_smul]
    rw [← key]
    have hpt : ∀ u : ℝ, (Complex.exp (↑(-2 * π * u * t) * Complex.I) • (ρ u : ℂ)).im =
        -(ρ u * Real.sin (2 * π * t * u)) := by
      intro u
      have harg : -2 * π * u * t = -(2 * π * t * u) := by ring
      simp only [smul_eq_mul, Complex.mul_im, Complex.exp_ofReal_mul_I_re,
        Complex.exp_ofReal_mul_I_im, Complex.ofReal_re, Complex.ofReal_im, harg,
        Real.sin_neg]
      ring
    simp only [hpt, integral_neg, hρ.integral_mul_sin t, neg_zero]
  apply Complex.ext
  · simp [mollifierFT]
  · simp [him]

/-- The Fourier transform of an even mollifier at `0` is its total mass, which is one. -/
lemma mollifierFT_zero (hρ : IsCircleMollifier ρ) : mollifierFT ρ 0 = 1 := by
  rw [mollifierFT_eq_integral_cos hρ 0]
  simp only [zero_mul, mul_zero, Real.cos_zero, mul_one]
  exact hρ.2.2.2.2

/-- The transform is bounded by the total mass of `|ρ|`, which is one. -/
lemma mollifierFT_abs_le_one (hρ : IsCircleMollifier ρ) (t : ℝ) : |mollifierFT ρ t| ≤ 1 := by
  rw [mollifierFT_eq_integral_cos hρ t]
  have hbound : ∀ u : ℝ, ‖ρ u * Real.cos (2 * π * t * u)‖ ≤ ρ u := fun u => by
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hρ.2.2.1 u)]
    exact mul_le_of_le_one_right (hρ.2.2.1 u) (Real.abs_cos_le_one _)
  have h := norm_integral_le_of_norm_le hρ.integrable (Filter.Eventually.of_forall hbound)
  rw [hρ.2.2.2.2, Real.norm_eq_abs] at h
  exact h

/-- The cosine factor is continuous and bounded by one, so `ρ(u) cos(2π t u)` is integrable. -/
lemma integrable_mollifier_mul_cos (hρ : IsCircleMollifier ρ) (t : ℝ) :
    Integrable (fun u => ρ u * Real.cos (2 * π * t * u)) :=
  hρ.integrable_mul (by fun_prop) (c := 1) fun u => Real.abs_cos_le_one _

/-- The identity `1 - ρ̂(t) = ∫ ρ(u) (1 - cos(2π t u)) du`, from unit mass. -/
lemma one_sub_mollifierFT (hρ : IsCircleMollifier ρ) (t : ℝ) :
    1 - mollifierFT ρ t = ∫ u, ρ u * (1 - Real.cos (2 * π * t * u)) := by
  have h1 : ∫ u, ρ u * (1 - Real.cos (2 * π * t * u)) =
      (∫ u, ρ u) - ∫ u, ρ u * Real.cos (2 * π * t * u) := by
    rw [← integral_sub hρ.integrable (integrable_mollifier_mul_cos hρ t)]
    congr 1
    ext u
    ring
  rw [h1, hρ.2.2.2.2, mollifierFT_eq_integral_cos hρ t]

/-- The transform satisfies `ρ̂(t) ≤ 1`, so `1 - ρ̂(t)` is nonnegative. -/
lemma mollifierFT_one_sub_nonneg (hρ : IsCircleMollifier ρ) (t : ℝ) : 0 ≤ 1 - mollifierFT ρ t := by
  rw [one_sub_mollifierFT hρ t]
  exact integral_nonneg fun u =>
    mul_nonneg (hρ.2.2.1 u) (by linarith [Real.cos_le_one (2 * π * t * u)])

/-- Pointwise bound `1 - cos(2π t u) ≤ 8 min(t², 1)` for `|u| ≤ 1/2`, from `1 - cos x ≤ x²/2`
and `1 - cos x ≤ 2`. -/
lemma one_sub_cos_le_of_abs_le {t u : ℝ} (hu : |u| ≤ 1 / 2) :
    1 - Real.cos (2 * π * t * u) ≤ 8 * min (t ^ 2) 1 := by
  have hquad : 1 - Real.cos (2 * π * t * u) ≤ (2 * π * t * u) ^ 2 / 2 := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := 2 * π * t * u)]
  have hcos : 1 - Real.cos (2 * π * t * u) ≤ 2 := by
    linarith [Real.neg_one_le_cos (2 * π * t * u)]
  have hu2 : u ^ 2 ≤ 1 / 4 := by
    have := abs_le.mp hu
    nlinarith
  have hpi : π ^ 2 ≤ 16 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
  rcases le_total (t ^ 2) 1 with ht | ht
  · rw [min_eq_left ht]
    have hsq : (2 * π * t * u) ^ 2 / 2 = 2 * π ^ 2 * t ^ 2 * u ^ 2 := by ring
    have h1 : 2 * π ^ 2 * t ^ 2 * u ^ 2 ≤ 2 * π ^ 2 * t ^ 2 * (1 / 4) :=
      mul_le_mul_of_nonneg_left hu2 (by positivity)
    have h2 : π ^ 2 * t ^ 2 ≤ 16 * t ^ 2 := mul_le_mul_of_nonneg_right hpi (sq_nonneg t)
    linarith
  · rw [min_eq_right ht]
    linarith

/-- The transform satisfies `0 ≤ 1 - ρ̂(t) ≤ 8 min(t², 1)`. -/
lemma mollifierFT_one_sub_le (hρ : IsCircleMollifier ρ) (t : ℝ) :
    1 - mollifierFT ρ t ≤ 8 * min (t ^ 2) 1 := by
  rw [one_sub_mollifierFT hρ t]
  have hint1 : Integrable (fun u => ρ u * (1 - Real.cos (2 * π * t * u))) :=
    hρ.integrable_mul (by fun_prop) (c := 2) fun u => by
      rw [abs_le]
      constructor <;> linarith [Real.cos_le_one (2 * π * t * u), Real.neg_one_le_cos (2 * π * t * u)]
  have hint2 : Integrable (fun u => ρ u * (8 * min (t ^ 2) 1)) := hρ.integrable.mul_const _
  calc ∫ u, ρ u * (1 - Real.cos (2 * π * t * u))
      ≤ ∫ u, ρ u * (8 * min (t ^ 2) 1) := by
        refine integral_mono hint1 hint2 fun u => ?_
        by_cases hu : ρ u = 0
        · simp [hu]
        · exact mul_le_mul_of_nonneg_left
            (one_sub_cos_le_of_abs_le (hρ.abs_lt_of_ne_zero hu).le) (hρ.2.2.1 u)
    _ = 8 * min (t ^ 2) 1 := by
        rw [integral_mul_const, hρ.2.2.2.2, one_mul]

/-- The squared bound `(1 - ρ̂(t))² ≤ 16 min(t², 1)`. -/
lemma mollifierFT_sq_one_sub_le (hρ : IsCircleMollifier ρ) (t : ℝ) :
    (1 - mollifierFT ρ t) ^ 2 ≤ 16 * min (t ^ 2) 1 := by
  have h0 := mollifierFT_one_sub_nonneg hρ t
  have h1 := mollifierFT_one_sub_le hρ t
  have hm := abs_le.mp (mollifierFT_abs_le_one hρ t)
  nlinarith [mul_nonneg h0 (show 0 ≤ 1 + mollifierFT ρ t by linarith [hm.1])]

/-- The squared bound `1 - ρ̂(t)² ≤ 16 min(t², 1)`. -/
lemma one_sub_mollifierFT_sq_le (hρ : IsCircleMollifier ρ) (t : ℝ) :
    1 - mollifierFT ρ t ^ 2 ≤ 16 * min (t ^ 2) 1 := by
  have h0 := mollifierFT_one_sub_nonneg hρ t
  have h1 := mollifierFT_one_sub_le hρ t
  nlinarith [sq_nonneg (1 - mollifierFT ρ t)]

/-- The transform squared is at most one. -/
lemma mollifierFT_sq_le_one (hρ : IsCircleMollifier ρ) (t : ℝ) : mollifierFT ρ t ^ 2 ≤ 1 := by
  have hm := abs_le.mp (mollifierFT_abs_le_one hρ t)
  nlinarith

/-- For `0 < r ≤ 1`, the function `min(t², 1)` is bounded by `|t|^(2r)`. -/
lemma min_sq_le_abs_rpow {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (t : ℝ) :
    min (t ^ 2) 1 ≤ |t| ^ (2 * r) := by
  rcases le_total |t| 1 with ht | ht
  · have hsq : |t| ^ (2 : ℝ) = t ^ 2 := by rw [Real.rpow_two, sq_abs]
    have hmono : |t| ^ (2 : ℝ) ≤ |t| ^ (2 * r) :=
      Real.rpow_le_rpow_of_exponent_ge' (abs_nonneg t) ht (by linarith) (by linarith)
    calc min (t ^ 2) 1 ≤ t ^ 2 := min_le_left _ _
      _ = |t| ^ (2 : ℝ) := hsq.symm
      _ ≤ |t| ^ (2 * r) := hmono
  · have h1 : (1 : ℝ) ≤ |t| ^ (2 * r) := Real.one_le_rpow ht (by linarith)
    exact (min_le_right _ _).trans h1

end Riesz1

end
