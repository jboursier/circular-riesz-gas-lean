/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Fourier analysis of the transport on `[0, 1]`

Fourier coefficients of functions on `ℝ` restricted to `[0, 1]`, with the normalization of
`fourierCoeff` on the unit circle. This file records the facts used by the mean-field energy
identity: change of variables for a translation, the derivative identity for smooth
periodic profiles, Parseval's identity for a translated difference, and the polarization
identity for two real `L²` profiles.
-/

public section

open MeasureTheory Set Complex Filter Topology
open scoped Real ComplexConjugate

namespace Riesz1

/-- The Fourier coefficient of a function on `ℝ` over one period `[0, 1]`. -/
@[expose] noncomputable def lineCoeff (f : ℝ → ℂ) (n : ℤ) : ℂ :=
  ∫ x in (0 : ℝ)..1, cexp (-(2 * π * I * n * x)) * f x

/-- The one-period coefficient agrees with Mathlib's coefficient on `[0, 1]`. -/
lemma fourierCoeffOn_eq_lineCoeff (f : ℝ → ℂ) (n : ℤ) :
    fourierCoeffOn zero_lt_one f n = lineCoeff f n := by
  rw [fourierCoeffOn_eq_integral, lineCoeff]
  have h1 : (1 / (1 - (0 : ℝ))) = 1 := by norm_num
  rw [h1, one_smul]
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only [fourier_coe_apply, smul_eq_mul]
  congr 1
  push_cast
  ring_nf

/-- A circle coefficient is the one-period coefficient of its lift. -/
lemma fourierCoeff_eq_lineCoeff (F : UnitAddCircle → ℂ) (n : ℤ) :
    fourierCoeff F n = lineCoeff (fun x : ℝ => F (x : UnitAddCircle)) n := by
  rw [fourierCoeff_eq_intervalIntegral F n 0, lineCoeff]
  simp only [zero_add, div_one, one_smul, smul_eq_mul]
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only [fourier_coe_apply]
  congr 1
  push_cast
  ring_nf

/-- The integrand of a coefficient is interval integrable as soon as the profile is. -/
lemma intervalIntegrable_exp_mul {f : ℝ → ℂ} (hf : IntervalIntegrable f volume 0 1) (n : ℤ) :
    IntervalIntegrable (fun x : ℝ => cexp (-(2 * π * I * n * x)) * f x) volume 0 1 :=
  hf.continuousOn_mul (by fun_prop : Continuous fun x : ℝ => cexp (-(2 * π * I * n * x))).continuousOn

/-- Coefficients are additive in the profile. -/
lemma lineCoeff_add {f g : ℝ → ℂ} (hf : IntervalIntegrable f volume 0 1)
    (hg : IntervalIntegrable g volume 0 1) (n : ℤ) :
    lineCoeff (fun x => f x + g x) n = lineCoeff f n + lineCoeff g n := by
  unfold lineCoeff
  rw [← intervalIntegral.integral_add (intervalIntegrable_exp_mul hf n)
    (intervalIntegrable_exp_mul hg n)]
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only [mul_add]

/-- Coefficients are additive in the profile, with a subtraction. -/
lemma lineCoeff_sub {f g : ℝ → ℂ} (hf : IntervalIntegrable f volume 0 1)
    (hg : IntervalIntegrable g volume 0 1) (n : ℤ) :
    lineCoeff (fun x => f x - g x) n = lineCoeff f n - lineCoeff g n := by
  unfold lineCoeff
  rw [← intervalIntegral.integral_sub (intervalIntegrable_exp_mul hf n)
    (intervalIntegrable_exp_mul hg n)]
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only [mul_sub]

/-- The exponential factor of a period-one integer frequency is one at the endpoint. -/
lemma cexp_neg_int_two_pi_mul_I (n : ℤ) :
    cexp (-(2 * π * I * n * (1 : ℝ))) = 1 := by
  have h := Complex.exp_int_mul_two_pi_mul_I (-n)
  rw [← h]
  congr 1
  push_cast
  ring

/-- Translation by `r` multiplies the coefficient of a periodic profile by `e^{-2πi n r}`. -/
lemma lineCoeff_comp_sub {f : ℝ → ℂ} (hf : Function.Periodic f 1) (r : ℝ) (n : ℤ) :
    lineCoeff (fun x => f (x - r)) n = cexp (-(2 * π * I * n * r)) * lineCoeff f n := by
  set g : ℝ → ℂ := fun y => cexp (-(2 * π * I * n * (y + r))) * f y with hg_def
  have hgp : Function.Periodic g 1 := by
    intro y
    simp only [hg_def]
    rw [hf y]
    push_cast
    have : cexp (-(2 * π * I * n * (y + 1 + r))) =
        cexp (-(2 * π * I * n * (y + r))) * cexp (-(2 * π * I * n * 1)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    rw [this]
    have h1 : cexp (-(2 * π * I * n * 1)) = 1 := by simpa using cexp_neg_int_two_pi_mul_I n
    rw [h1, mul_one]
  have hL : lineCoeff (fun x => f (x - r)) n = ∫ x in (0 : ℝ)..1, g (x - r) := by
    unfold lineCoeff
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [hg_def]
    congr 2
    push_cast
    ring
  rw [hL, intervalIntegral.integral_comp_sub_right g r]
  have hper := hgp.intervalIntegral_add_eq (-r) 0
  rw [show (0 : ℝ) - r = -r by ring, show (1 : ℝ) - r = -r + 1 by ring, hper, zero_add]
  unfold lineCoeff
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only [hg_def]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- The derivative of a smooth periodic profile has coefficients `2 π i n` times those of the
profile. -/
lemma lineCoeff_deriv {ξ : ℝ → ℝ} (hξ : ContDiff ℝ 1 ξ) (hp : Function.Periodic ξ 1) (n : ℤ) :
    lineCoeff (fun x : ℝ => ((deriv ξ x : ℝ) : ℂ)) n =
      2 * π * I * n * lineCoeff (fun x : ℝ => (ξ x : ℂ)) n := by
  have hu : ∀ x : ℝ, HasDerivAt (fun y : ℝ => cexp (-(2 * π * I * n * y)))
      (-(2 * π * I * n) * cexp (-(2 * π * I * n * x))) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => -(2 * π * I * n * (y : ℂ))) (-(2 * π * I * n)) x := by
      have := (((hasDerivAt_id x).ofReal_comp).const_mul (2 * π * I * n)).neg
      convert this using 1
      · ext y
        simp
      · simp
    have h2 := h1.cexp
    convert h2 using 1
    ring
  have hv : ∀ x : ℝ, HasDerivAt (fun y : ℝ => (ξ y : ℂ)) ((deriv ξ x : ℝ) : ℂ) x := by
    intro x
    exact ((hξ.differentiable (by norm_num) x).hasDerivAt).ofReal_comp
  have hu'c : Continuous fun x : ℝ => -(2 * π * I * n) * cexp (-(2 * π * I * n * x)) := by
    fun_prop
  have hv'c : Continuous fun x : ℝ => ((deriv ξ x : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (hξ.continuous_deriv (by norm_num))
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := 0) (b := 1) (fun x _ => hu x) (fun x _ => hv x)
    (hu'c.intervalIntegrable 0 1) (hv'c.intervalIntegrable 0 1)
  have hu1 : cexp (-(2 * π * I * n * ((1 : ℝ) : ℂ))) = 1 := cexp_neg_int_two_pi_mul_I n
  have hu0 : cexp (-(2 * π * I * n * ((0 : ℝ) : ℂ))) = 1 := by simp
  have hv1 : (ξ 1 : ℂ) = (ξ 0 : ℂ) := by
    have := hp 0
    simp only [zero_add] at this
    rw [this]
  have hbd : cexp (-(2 * π * I * n * ((1 : ℝ) : ℂ))) * (ξ 1 : ℂ) -
      cexp (-(2 * π * I * n * ((0 : ℝ) : ℂ))) * (ξ 0 : ℂ) = 0 := by
    rw [hu1, hu0, hv1]
    ring
  have hconst : ∫ x in (0 : ℝ)..1, -(2 * π * I * n) * cexp (-(2 * π * I * n * x)) * (ξ x : ℂ) =
      -(2 * π * I * n) * ∫ x in (0 : ℝ)..1, cexp (-(2 * π * I * n * x)) * (ξ x : ℂ) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    ring
  unfold lineCoeff
  rw [hbd, zero_sub, hconst] at hIBP
  rw [hIBP]
  ring

/-- An `L²` profile on `(0, 1]` is interval integrable on `[0, 1]`. -/
lemma intervalIntegrable_of_memLp {f : ℝ → ℂ} (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1))) :
    IntervalIntegrable f volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  exact (hf.integrable one_le_two)

/-- Parseval's identity on one period, for a profile which is square integrable on `(0, 1]`. -/
lemma hasSum_sq_lineCoeff {f : ℝ → ℂ} (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) 1))) :
    HasSum (fun k : ℤ => ‖lineCoeff f k‖ ^ 2) (∫ x in (0 : ℝ)..1, ‖f x‖ ^ 2) := by
  have h := hasSum_sq_fourierCoeffOn zero_lt_one hf
  simp only [sub_zero, inv_one, one_smul, fourierCoeffOn_eq_lineCoeff] at h
  exact h

/-- A circle `L²` function has an `L²` lift on `(0, 1]`. -/
lemma memLp_Ioc_of_circle {F : UnitAddCircle → ℂ} (hF : MemLp F 2 volume) :
    MemLp (fun x : ℝ => F (x : UnitAddCircle)) 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have hmp := AddCircle.measurePreserving_mk (1 : ℝ) 0
  have h := hF.comp_measurePreserving hmp
  have h2 : MemLp (F ∘ (QuotientAddGroup.mk : ℝ → UnitAddCircle)) 2
      (volume.restrict (Ioc (0 : ℝ) 1)) := by
    simpa using h
  exact h2

/-- The modulus of `1 - e^{-2π i n r}`, squared. -/
lemma norm_one_sub_cexp_sq (n : ℤ) (r : ℝ) :
    ‖1 - cexp (-(2 * π * I * n * r))‖ ^ 2 = 2 - 2 * Real.cos (2 * π * n * r) := by
  have hre : (1 - cexp (-(2 * π * I * n * r))).re = 1 - Real.cos (2 * π * n * r) := by
    rw [Complex.sub_re, Complex.one_re, Complex.exp_re]
    have hz : (-(2 * π * I * n * r) : ℂ).re = 0 := by simp
    have hzi : (-(2 * π * I * n * r) : ℂ).im = -(2 * π * n * r) := by simp
    rw [hz, hzi, Real.exp_zero, one_mul, Real.cos_neg]
  have him : (1 - cexp (-(2 * π * I * n * r))).im = Real.sin (2 * π * n * r) := by
    have hz : (-(2 * π * I * n * r) : ℂ).re = 0 := by simp
    have hzi : (-(2 * π * I * n * r) : ℂ).im = -(2 * π * n * r) := by simp
    rw [Complex.sub_im, Complex.one_im, Complex.exp_im, hz, hzi, Real.exp_zero, Real.sin_neg]
    ring
  rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
  nlinarith [Real.sin_sq_add_cos_sq (2 * π * n * r)]

/-- Parseval's identity for the difference of a circle profile and its translate. -/
lemma hasSum_translate_sq {F : UnitAddCircle → ℂ} (hF : MemLp F 2 volume) (r : ℝ) :
    HasSum (fun k : ℤ => ‖fourierCoeff F k‖ ^ 2 * (2 - 2 * Real.cos (2 * π * k * r)))
      (∫ x in (0 : ℝ)..1, ‖F (x : UnitAddCircle) - F ((x - r : ℝ) : UnitAddCircle)‖ ^ 2) := by
  set φ : ℝ → ℂ := fun x => F (x : UnitAddCircle) with hφ
  have hφp : Function.Periodic φ 1 := fun x => by simp [hφ]
  have hFr : MemLp (fun y : UnitAddCircle => F (y - (r : UnitAddCircle))) 2 volume :=
    hF.comp_measurePreserving (measurePreserving_sub_right volume (r : UnitAddCircle))
  have hφr : MemLp (fun x : ℝ => φ (x - r)) 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
    have h := memLp_Ioc_of_circle hFr
    have hfun : (fun x : ℝ => F ((x : UnitAddCircle) - (r : UnitAddCircle))) =
        fun x : ℝ => φ (x - r) := by
      funext x
      simp only [hφ]
      congr 1
    rw [hfun] at h
    exact h
  have hφL : MemLp φ 2 (volume.restrict (Ioc (0 : ℝ) 1)) := memLp_Ioc_of_circle hF
  have hD : MemLp (fun x : ℝ => φ x - φ (x - r)) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    hφL.sub hφr
  have hcoeff : ∀ k : ℤ, lineCoeff (fun x => φ x - φ (x - r)) k =
      (1 - cexp (-(2 * π * I * k * r))) * fourierCoeff F k := by
    intro k
    rw [lineCoeff_sub (intervalIntegrable_of_memLp hφL) (intervalIntegrable_of_memLp hφr) k,
      lineCoeff_comp_sub hφp r k, fourierCoeff_eq_lineCoeff F k]
    ring
  have h := hasSum_sq_lineCoeff hD
  have hfun : (fun k : ℤ => ‖fourierCoeff F k‖ ^ 2 * (2 - 2 * Real.cos (2 * π * k * r))) =
      fun k : ℤ => ‖lineCoeff (fun x => φ x - φ (x - r)) k‖ ^ 2 := by
    funext k
    rw [hcoeff k, norm_mul, mul_pow, norm_one_sub_cexp_sq k r]
    ring
  rw [hfun]
  exact h

/-- Polarization in the complex numbers. -/
lemma norm_add_sq_sub_sq_complex (a b : ℂ) :
    ‖a + b‖ ^ 2 - ‖a - b‖ ^ 2 = 4 * (conj a * b).re := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- Parseval's identity for the product of two real `L²` profiles on one period: the coefficient
sum of `conj(û) v̂` is the integral of `u v`. -/
lemma hasSum_re_conj_mul {u v : ℝ → ℝ}
    (hu : MemLp (fun x => (u x : ℂ)) 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hv : MemLp (fun x => (v x : ℂ)) 2 (volume.restrict (Ioc (0 : ℝ) 1))) :
    HasSum (fun k : ℤ => (conj (lineCoeff (fun x => (u x : ℂ)) k) *
      lineCoeff (fun x => (v x : ℂ)) k).re) (∫ x in (0 : ℝ)..1, u x * v x) := by
  have huI := intervalIntegrable_of_memLp hu
  have hvI := intervalIntegrable_of_memLp hv
  have hsum : MemLp (fun x => (u x : ℂ) + (v x : ℂ)) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    hu.add hv
  have hdif : MemLp (fun x => (u x : ℂ) - (v x : ℂ)) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    hu.sub hv
  have hp := hasSum_sq_lineCoeff hsum
  have hm := hasSum_sq_lineCoeff hdif
  have hcAdd : ∀ k : ℤ, lineCoeff (fun x => (u x : ℂ) + (v x : ℂ)) k =
      lineCoeff (fun x => (u x : ℂ)) k + lineCoeff (fun x => (v x : ℂ)) k :=
    fun k => lineCoeff_add huI hvI k
  have hcSub : ∀ k : ℤ, lineCoeff (fun x => (u x : ℂ) - (v x : ℂ)) k =
      lineCoeff (fun x => (u x : ℂ)) k - lineCoeff (fun x => (v x : ℂ)) k :=
    fun k => lineCoeff_sub huI hvI k
  have hpt : ∀ x : ℝ, ‖(u x : ℂ) + (v x : ℂ)‖ ^ 2 - ‖(u x : ℂ) - (v x : ℂ)‖ ^ 2 =
      4 * (u x * v x) := by
    intro x
    rw [norm_add_sq_sub_sq_complex]
    simp [← Complex.ofReal_mul]
  have hIi : IntervalIntegrable (fun x => ‖(u x : ℂ) + (v x : ℂ)‖ ^ 2) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact hsum.integrable_norm_pow'
  have hIm : IntervalIntegrable (fun x => ‖(u x : ℂ) - (v x : ℂ)‖ ^ 2) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact hdif.integrable_norm_pow'
  have hIuv : (∫ x in (0 : ℝ)..1, ‖(u x : ℂ) + (v x : ℂ)‖ ^ 2) -
      ∫ x in (0 : ℝ)..1, ‖(u x : ℂ) - (v x : ℂ)‖ ^ 2 = 4 * ∫ x in (0 : ℝ)..1, u x * v x := by
    rw [← intervalIntegral.integral_sub hIi hIm, ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun x _ => hpt x
  have hterm : ∀ k : ℤ, (1 / 4 : ℝ) * (‖lineCoeff (fun x => (u x : ℂ) + (v x : ℂ)) k‖ ^ 2 -
      ‖lineCoeff (fun x => (u x : ℂ) - (v x : ℂ)) k‖ ^ 2) =
      (conj (lineCoeff (fun x => (u x : ℂ)) k) * lineCoeff (fun x => (v x : ℂ)) k).re := by
    intro k
    rw [hcAdd k, hcSub k, norm_add_sq_sub_sq_complex]
    ring
  have hH := (hp.sub hm).mul_left (1 / 4 : ℝ)
  have hfun : (fun k : ℤ => (conj (lineCoeff (fun x => (u x : ℂ)) k) *
      lineCoeff (fun x => (v x : ℂ)) k).re) =
      fun k : ℤ => (1 / 4 : ℝ) * (‖lineCoeff (fun x => (u x : ℂ) + (v x : ℂ)) k‖ ^ 2 -
        ‖lineCoeff (fun x => (u x : ℂ) - (v x : ℂ)) k‖ ^ 2) := by
    funext k
    exact (hterm k).symm
  have hval : ∫ x in (0 : ℝ)..1, u x * v x =
      (1 / 4 : ℝ) * ((∫ x in (0 : ℝ)..1, ‖(u x : ℂ) + (v x : ℂ)‖ ^ 2) -
        ∫ x in (0 : ℝ)..1, ‖(u x : ℂ) - (v x : ℂ)‖ ^ 2) := by
    rw [hIuv]
    ring
  rw [hfun, hval]
  exact hH

end Riesz1
