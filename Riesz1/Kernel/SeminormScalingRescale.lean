/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.SeminormScalingCore

/-!
# Rescaling of the line seminorm and of the `L¹` norm

For a scale `ℓ > 0`, the function `z ↦ f(z/ℓ)` has Fourier transform `ℓ 𝓕f(ℓη)`. Its weighted
seminorm with weight `|η|^τ` is `ℓ^{1-τ}` times that of `f`, and its `L¹` norm is `ℓ` times
that of `f`. An `L¹` norm of a function supported in an interval of length `L` is bounded by
the square root of `L` times its `L²` norm.
-/

public section

open MeasureTheory Set FourierTransform
open scoped ENNReal ComplexConjugate

namespace Riesz1

/-- The Fourier transform of a rescaled function. -/
theorem fourier_rescale (f : ℝ → ℂ) {ℓ : ℝ} (hℓ : 0 < ℓ) (η : ℝ) :
    𝓕 (fun z => f (z / ℓ)) η = (ℓ : ℂ) * 𝓕 f (ℓ * η) := by
  have hin : ∀ a b : ℝ, inner ℝ a b = a * b := fun a b => by simp [mul_comm]
  have hpt : ∀ x : ℝ, Real.fourierChar (-(inner ℝ (ℓ * x) η)) • f (ℓ * x / ℓ) =
      Real.fourierChar (-(inner ℝ x (ℓ * η))) • f x := by
    intro x
    have hcancel : ℓ * x / ℓ = x := mul_div_cancel_left₀ x hℓ.ne'
    rw [hcancel, hin, hin]
    congr 2
    ring
  have h := Measure.integral_comp_mul_left
    (fun v : ℝ => Real.fourierChar (-(inner ℝ v η)) • f (v / ℓ)) ℓ
  simp only [hpt] at h
  rw [abs_of_pos (inv_pos.mpr hℓ)] at h
  rw [Real.fourier_eq, Real.fourier_eq]
  rw [Complex.real_smul] at h
  simp only [Circle.smul_def, smul_eq_mul] at h ⊢
  have hℓc : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ.ne'
  rw [h]
  push_cast
  field_simp

/-- Scaling of a lower integral by a positive factor. -/
theorem lintegral_comp_mul_left_real {H : ℝ → ENNReal} (hH : Measurable H) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∫⁻ η, H (ℓ * η) = ENNReal.ofReal ℓ⁻¹ * ∫⁻ ζ, H ζ := by
  have hm : Measurable (fun η : ℝ => ℓ * η) := measurable_const_mul ℓ
  rw [← lintegral_map hH hm, Real.map_volume_mul_left hℓ.ne', lintegral_smul_measure,
    abs_of_pos (inv_pos.mpr hℓ), smul_eq_mul]

/-- The weighted line seminorm of a rescaled function is `ℓ^{1-τ}` times that of the original. -/
theorem lintegral_line_seminorm_rescale {τ : ℝ} (hτ2 : τ < 2) {f : ℝ → ℂ}
    (hcont : Continuous (𝓕 f)) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∫⁻ η, ENNReal.ofReal (|η| ^ τ * ‖𝓕 (fun z => f (z / ℓ)) η‖ ^ 2) =
      ENNReal.ofReal (ℓ ^ (1 - τ)) * ∫⁻ η, ENNReal.ofReal (|η| ^ τ * ‖𝓕 f η‖ ^ 2) := by
  set H : ℝ → ENNReal := fun ζ => ENNReal.ofReal (|ζ| ^ τ * ℓ ^ (2 - τ) * ‖𝓕 f ζ‖ ^ 2) with hHdef
  have hH : Measurable H := by
    have hm : Measurable (𝓕 f) := hcont.measurable
    fun_prop
  have hpt : ∀ η : ℝ, ENNReal.ofReal (|η| ^ τ * ‖𝓕 (fun z => f (z / ℓ)) η‖ ^ 2) =
      H (ℓ * η) := by
    intro η
    rw [fourier_rescale f hℓ η, norm_mul, Complex.norm_real, Real.norm_of_nonneg hℓ.le, mul_pow]
    simp only [hHdef]
    congr 1
    rw [abs_mul, abs_of_pos hℓ, Real.mul_rpow hℓ.le (abs_nonneg η)]
    have hAB : ℓ ^ τ * ℓ ^ (2 - τ) = ℓ ^ 2 := by
      rw [← Real.rpow_add hℓ]
      norm_num
    linear_combination (-(|η| ^ τ * ‖𝓕 f (ℓ * η)‖ ^ 2)) * hAB
  simp_rw [hpt]
  rw [lintegral_comp_mul_left_real hH hℓ]
  have hsplit : ∫⁻ ζ, H ζ = ENNReal.ofReal (ℓ ^ (2 - τ)) *
      ∫⁻ ζ, ENNReal.ofReal (|ζ| ^ τ * ‖𝓕 f ζ‖ ^ 2) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr (fun ζ => ?_)
    simp only [hHdef]
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hℓ.le _)]
    congr 1
    ring
  rw [hsplit, ← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr hℓ.le)]
  congr 2
  have h1 : ℓ ^ (2 - τ) = ℓ * ℓ ^ (1 - τ) := by
    rw [← Real.rpow_one_add' hℓ.le (ne_of_gt (by linarith))]
    congr 1
    ring
  rw [h1]
  field_simp

/-- The `L¹` norm of a rescaled function is `ℓ` times that of the original. -/
theorem integral_norm_rescale (f : ℝ → ℂ) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∫ z, ‖f (z / ℓ)‖ = ℓ * ∫ z, ‖f z‖ := by
  have h := Measure.integral_comp_mul_left (fun v => ‖f v‖) ℓ⁻¹
  simp only [inv_inv, abs_of_pos hℓ, smul_eq_mul] at h
  simpa [div_eq_inv_mul] using h

/-- Cauchy–Schwarz for functions supported in an interval: the `L¹` norm squared is at most the
length times the `L²` norm squared. -/
theorem integral_norm_sq_le {ξ : ℝ → ℂ} {L : ℝ} (hL : 0 ≤ L) (hξ : MemLp ξ 2 volume)
    (hsupp : ∀ x : ℝ, L < |x| → ξ x = 0) :
    (∫ x, ‖ξ x‖) ^ 2 ≤ (2 * L) * ∫ x, ‖ξ x‖ ^ 2 := by
  set I : Set ℝ := Icc (-L) L with hI
  set f : ℝ → ℝ := I.indicator (fun _ => (1 : ℝ)) with hf
  have hfg : ∀ x, f x * ‖ξ x‖ = ‖ξ x‖ := by
    intro x
    by_cases hx : x ∈ I
    · simp [hf, hx]
    · have hxL : L < |x| := by
        rw [hI, mem_Icc, not_and_or, not_le, not_le] at hx
        rcases hx with h | h
        · rw [abs_of_neg (by linarith)]
          linarith
        · rw [abs_of_pos (by linarith)]
          linarith
      simp [hf, hx, hsupp x hxL]
  have hf2 : MemLp f (ENNReal.ofReal 2) volume := by
    rw [show ENNReal.ofReal 2 = 2 by norm_num]
    refine memLp_indicator_const 2 measurableSet_Icc.nullMeasurableSet 1 (Or.inr ?_)
    simp
  have hg2 : MemLp (fun x => ‖ξ x‖) (ENNReal.ofReal 2) volume := by
    rw [show ENNReal.ofReal 2 = 2 by norm_num]
    exact hξ.norm
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (f := f) (g := fun x => ‖ξ x‖)
    (ae_of_all _ (fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x))
    (ae_of_all _ (fun x => norm_nonneg _)) hf2 hg2
  have hlhs : ∫ x, f x * ‖ξ x‖ = ∫ x, ‖ξ x‖ := integral_congr_ae (ae_of_all _ hfg)
  have hfint : ∫ x, f x ^ (2 : ℝ) = 2 * L := by
    have h1 : ∀ x, f x ^ (2 : ℝ) = I.indicator (fun _ => (1 : ℝ)) x := by
      intro x
      rw [Real.rpow_two]
      by_cases hx : x ∈ I <;> simp [hf, hx]
    simp only [h1]
    rw [hI, integral_indicator_const (1 : ℝ) measurableSet_Icc, smul_eq_mul, mul_one,
      Real.volume_real_Icc]
    rw [max_eq_left (by linarith)]
    ring
  have hgint : ∫ x, ‖ξ x‖ ^ (2 : ℝ) = ∫ x, ‖ξ x‖ ^ 2 := by
    congr 1
    funext x
    rw [Real.rpow_two]
  rw [hlhs, hfint, hgint] at hH
  have hB : 0 ≤ ∫ x, ‖ξ x‖ ^ 2 := integral_nonneg (fun x => sq_nonneg _)
  have hA : 0 ≤ ∫ x, ‖ξ x‖ := integral_nonneg (fun x => norm_nonneg _)
  have hX : (∫ x, ‖ξ x‖) ≤ Real.sqrt (2 * L) * Real.sqrt (∫ x, ‖ξ x‖ ^ 2) := by
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hH
    exact hH
  calc (∫ x, ‖ξ x‖) ^ 2 ≤ (Real.sqrt (2 * L) * Real.sqrt (∫ x, ‖ξ x‖ ^ 2)) ^ 2 :=
        pow_le_pow_left₀ hA hX 2
    _ = (2 * L) * ∫ x, ‖ξ x‖ ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by linarith), Real.sq_sqrt hB]

end Riesz1
