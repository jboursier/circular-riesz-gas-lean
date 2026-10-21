/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Lévy representation of the power `|η|^τ`

For `0 < τ < 1` the integral `∫ (1 - cos(2πv)) / |v|^{1+τ} dv` is finite and positive.
Scaling the variable turns the integrand at frequency `η` into `|η|^{1+τ}` times the
integrand at frequency `1`, so `|η|^τ` is a fixed positive multiple of the Lévy integral
of `1 - cos(2πηu)`. This representation converts the frequency-side weight `|η|^τ`
into a position-side kernel, which the cross-term estimate of the scaling lemma uses.
-/

public section

open MeasureTheory Real

namespace Riesz1

/-- The Lévy integral `∫ (1 - cos(2πv)) / |v|^{1+τ} dv`. -/
@[expose]
noncomputable def levyIntegral (τ : ℝ) : ℝ :=
  ∫ v : ℝ, (1 - Real.cos (2 * Real.pi * v)) / |v| ^ (1 + τ)

/-- The Lévy integrand is dominated by a multiple of `(1 + |v|)^{-(1+τ)}`. -/
private lemma levy_integrand_le {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (v : ℝ) :
    (1 - Real.cos (2 * Real.pi * v)) / |v| ^ (1 + τ) ≤
      2 * Real.pi ^ 2 * 2 ^ (1 + τ) * (1 + |v|) ^ (-(1 + τ)) := by
  have hT : 0 < (2 : ℝ) ^ (1 + τ) := by positivity
  have hnum2 : 1 - Real.cos (2 * Real.pi * v) ≤ 2 := by
    linarith [Real.neg_one_le_cos (2 * Real.pi * v)]
  have hnumsq : 1 - Real.cos (2 * Real.pi * v) ≤ 2 * Real.pi ^ 2 * v ^ 2 := by
    have h := Real.one_sub_sq_div_two_le_cos (x := 2 * Real.pi * v)
    nlinarith [h]
  have ha : 0 ≤ |v| := abs_nonneg v
  have hpi : (1 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have hdef : 2 * Real.pi ^ 2 * 2 ^ (1 + τ) * (1 + |v|) ^ (-(1 + τ)) =
      2 * Real.pi ^ 2 * 2 ^ (1 + τ) / (1 + |v|) ^ (1 + τ) := by
    rw [Real.rpow_neg (by linarith : (0 : ℝ) ≤ 1 + |v|)]
    ring
  rw [hdef]
  by_cases hv : v = 0
  · subst hv
    simp only [mul_zero, Real.cos_zero, sub_self, zero_div]
    positivity
  have hvpos : 0 < |v| := abs_pos.mpr hv
  have hP : 0 < |v| ^ (1 + τ) := Real.rpow_pos_of_pos hvpos _
  have hQ : 0 < (1 + |v|) ^ (1 + τ) := Real.rpow_pos_of_pos (by linarith) _
  rw [div_le_div_iff₀ hP hQ]
  rcases le_total |v| 1 with h1 | h1
  · -- Near the singularity: `N ≤ 2π² v² ≤ 2π² |v|^{1+τ}` and `(1 + |v|)^{1+τ} ≤ 2^{1+τ}`.
    have hsq : |v| ^ 2 ≤ |v| ^ (1 + τ) := by
      have := Real.rpow_le_rpow_of_exponent_ge hvpos h1 (show 1 + τ ≤ 2 by linarith)
      simpa [Real.rpow_two] using this
    have hv2 : v ^ 2 = |v| ^ 2 := (sq_abs v).symm
    have hN : 1 - Real.cos (2 * Real.pi * v) ≤ 2 * Real.pi ^ 2 * |v| ^ (1 + τ) := by
      have hπ : 0 ≤ 2 * Real.pi ^ 2 := by positivity
      nlinarith [hnumsq, hsq, hv2, hπ]
    have hQT : (1 + |v|) ^ (1 + τ) ≤ 2 ^ (1 + τ) :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
    calc (1 - Real.cos (2 * Real.pi * v)) * (1 + |v|) ^ (1 + τ)
        ≤ (2 * Real.pi ^ 2 * |v| ^ (1 + τ)) * (1 + |v|) ^ (1 + τ) :=
          mul_le_mul_of_nonneg_right hN hQ.le
      _ ≤ (2 * Real.pi ^ 2 * |v| ^ (1 + τ)) * 2 ^ (1 + τ) :=
          mul_le_mul_of_nonneg_left hQT (by positivity)
      _ = 2 * Real.pi ^ 2 * 2 ^ (1 + τ) * |v| ^ (1 + τ) := by ring
  · -- Far from the singularity: `N ≤ 2` and `(1 + |v|)^{1+τ} ≤ 2^{1+τ} |v|^{1+τ}`.
    have hle : (1 + |v|) ^ (1 + τ) ≤ 2 ^ (1 + τ) * |v| ^ (1 + τ) := by
      rw [← Real.mul_rpow (by norm_num) ha]
      exact Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
    calc (1 - Real.cos (2 * Real.pi * v)) * (1 + |v|) ^ (1 + τ)
        ≤ 2 * (1 + |v|) ^ (1 + τ) := mul_le_mul_of_nonneg_right hnum2 hQ.le
      _ ≤ 2 * (2 ^ (1 + τ) * |v| ^ (1 + τ)) := by linarith
      _ ≤ 2 * Real.pi ^ 2 * 2 ^ (1 + τ) * |v| ^ (1 + τ) := by
          have hTP : 0 ≤ 2 ^ (1 + τ) * |v| ^ (1 + τ) := by positivity
          nlinarith [hTP]

/-- The Lévy integrand is nonnegative. -/
private lemma levy_integrand_nonneg {τ : ℝ} (v : ℝ) :
    0 ≤ (1 - Real.cos (2 * Real.pi * v)) / |v| ^ (1 + τ) :=
  div_nonneg (by linarith [Real.cos_le_one (2 * Real.pi * v)])
    (Real.rpow_nonneg (abs_nonneg v) _)

/-- The Lévy integrand is integrable. -/
theorem integrable_levy_integrand {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    Integrable (fun v : ℝ => (1 - Real.cos (2 * Real.pi * v)) / |v| ^ (1 + τ)) := by
  have hint : Integrable (fun v : ℝ => (1 + |v|) ^ (-(1 + τ))) volume := by
    have h := integrable_one_add_norm (μ := volume) (E := ℝ) (r := 1 + τ) (by simp; linarith)
    simpa [Real.norm_eq_abs] using h
  refine Integrable.mono' (hint.const_mul (2 * Real.pi ^ 2 * 2 ^ (1 + τ))) ?_ ?_
  · have hm : Measurable (fun v : ℝ => (1 - Real.cos (2 * Real.pi * v)) / |v| ^ (1 + τ)) := by
      fun_prop
    exact hm.aestronglyMeasurable
  · refine ae_of_all _ (fun v => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (levy_integrand_nonneg v)]
    exact levy_integrand_le hτ hτ1 v

/-- The Lévy integral is positive. -/
theorem levyIntegral_pos {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) : 0 < levyIntegral τ := by
  unfold levyIntegral
  rw [integral_pos_iff_support_of_nonneg (fun v => levy_integrand_nonneg v)
    (integrable_levy_integrand hτ hτ1)]
  refine lt_of_lt_of_le (b := volume (Set.Ioo (1 / 4 : ℝ) (1 / 2))) ?_ (measure_mono ?_)
  · rw [Real.volume_Ioo]
    norm_num
  · intro v hv
    simp only [Set.mem_Ioo] at hv
    simp only [Function.mem_support]
    have hcos : Real.cos (2 * Real.pi * v) < 1 := by
      have h := Real.cos_lt_cos_of_nonneg_of_le_pi (x := 0) (y := 2 * Real.pi * v)
        le_rfl (by nlinarith [Real.pi_gt_three, Real.pi_pos]) (by nlinarith [Real.pi_pos])
      simpa using h
    have hnum : 1 - Real.cos (2 * Real.pi * v) ≠ 0 := by linarith
    have hden : |v| ^ (1 + τ) ≠ 0 := by
      apply ne_of_gt
      apply Real.rpow_pos_of_pos
      rw [abs_pos]
      linarith [hv.1]
    exact div_ne_zero hnum hden

/-- Scaling of the Lévy integrand: the integral at frequency `η` is `|η|^τ` times the
Lévy integral. -/
theorem integral_levy_scale {τ : ℝ} (hτ : 0 < τ) (η : ℝ) :
    ∫ u : ℝ, (1 - Real.cos (2 * Real.pi * (η * u))) / |u| ^ (1 + τ) =
      |η| ^ τ * levyIntegral τ := by
  rcases eq_or_ne η 0 with hη | hη
  · subst hη
    simp only [zero_mul, mul_zero, Real.cos_zero, sub_self, zero_div, integral_zero,
      abs_zero]
    rw [Real.zero_rpow hτ.ne']
    ring
  have hpt : ∀ u : ℝ, (1 - Real.cos (2 * Real.pi * (η * u))) / |u| ^ (1 + τ) =
      |η| ^ (1 + τ) * ((1 - Real.cos (2 * Real.pi * (η * u))) / |η * u| ^ (1 + τ)) := by
    intro u
    rcases eq_or_ne u 0 with hu | hu
    · subst hu
      simp
    · rw [abs_mul, Real.mul_rpow (abs_nonneg η) (abs_nonneg u)]
      have hηp : |η| ^ (1 + τ) ≠ 0 := (Real.rpow_pos_of_pos (abs_pos.mpr hη) _).ne'
      have hup : |u| ^ (1 + τ) ≠ 0 := (Real.rpow_pos_of_pos (abs_pos.mpr hu) _).ne'
      field_simp
  have hcomp := Measure.integral_comp_mul_left
    (fun v : ℝ => (1 - Real.cos (2 * Real.pi * v)) / |v| ^ (1 + τ)) η
  have hI : ∫ y : ℝ, (1 - Real.cos (2 * Real.pi * y)) / |y| ^ (1 + τ) = levyIntegral τ := rfl
  have hrp : |η| ^ (1 + τ) = |η| * |η| ^ τ := by
    rw [Real.rpow_add (abs_pos.mpr hη), Real.rpow_one]
  simp_rw [hpt]
  rw [integral_const_mul, hcomp, hI, smul_eq_mul, abs_inv, hrp]
  field_simp

/-- The power `|η|^τ` is a fixed multiple of the Lévy integral at frequency `η`. -/
theorem rpow_abs_eq_levy_integral {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (η : ℝ) :
    |η| ^ τ = (levyIntegral τ)⁻¹ *
      ∫ u : ℝ, (1 - Real.cos (2 * Real.pi * (η * u))) / |u| ^ (1 + τ) := by
  have hI : levyIntegral τ ≠ 0 := (levyIntegral_pos hτ hτ1).ne'
  rw [integral_levy_scale hτ η]
  field_simp

/-- Pointwise scaling of the Lévy integrand: at frequency `η` the integrand is `|η|^{1+τ}` times
the integrand evaluated at `η u`. -/
theorem levy_integrand_eq_scale {τ : ℝ} (hτ : 0 < τ) (η u : ℝ) :
    (1 - Real.cos (2 * Real.pi * (η * u))) / |u| ^ (1 + τ) =
      |η| ^ (1 + τ) * ((1 - Real.cos (2 * Real.pi * (η * u))) / |η * u| ^ (1 + τ)) := by
  rcases eq_or_ne u 0 with hu | hu
  · subst hu
    simp [Real.zero_rpow (by linarith : (1 + τ) ≠ 0)]
  rcases eq_or_ne η 0 with hη | hη
  · subst hη
    simp [Real.zero_rpow (by linarith : (1 + τ) ≠ 0)]
  · have hηp : |η| ^ (1 + τ) ≠ 0 := (Real.rpow_pos_of_pos (abs_pos.mpr hη) _).ne'
    have hup : |u| ^ (1 + τ) ≠ 0 := (Real.rpow_pos_of_pos (abs_pos.mpr hu) _).ne'
    rw [abs_mul, Real.mul_rpow (abs_nonneg η) (abs_nonneg u)]
    field_simp

/-- The Lévy integrand at every frequency is integrable. -/
theorem integrable_levy_scaled {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (η : ℝ) :
    Integrable (fun u : ℝ => (1 - Real.cos (2 * Real.pi * (η * u))) / |u| ^ (1 + τ)) := by
  rcases eq_or_ne η 0 with hη | hη
  · subst hη
    have hz : (fun u : ℝ => (1 - Real.cos (2 * Real.pi * (0 * u))) / |u| ^ (1 + τ)) =
        fun _ => 0 := by
      funext u
      simp
    rw [hz]
    exact integrable_zero ℝ ℝ volume
  · have h := (integrable_levy_integrand hτ hτ1).comp_mul_left' hη
    refine (h.const_mul (|η| ^ (1 + τ))).congr (ae_of_all _ (fun u => ?_))
    exact (levy_integrand_eq_scale hτ η u).symm

end Riesz1
