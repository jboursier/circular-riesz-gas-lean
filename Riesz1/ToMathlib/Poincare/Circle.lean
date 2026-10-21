/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Poincaré (Wirtinger) inequality on a circle

Let `T > 0` and let `f : ℝ → ℝ` be a `C^1` function with period `T`. Then the squared
deviation of `f` from its mean over `[0, T]` is controlled by the derivative:
`∫₀ᵀ (f - m)² ≤ (T / 2π)² ∫₀ᵀ (f')²`, where `m = T⁻¹ ∫₀ᵀ f`.

For `T = 2π` this is Wirtinger's inequality. For a general period the proof works on the Fourier
side. Each nonzero frequency `n` of the centred function satisfies
`|ĝ(n)| = T |ĝ'(n)| / (2π |n|) ≤ (T / 2π) |ĝ'(n)|`, the zeroth frequency vanishes, and
Parseval's identity converts the coefficient bound into the integral bound.

The statement `integral_sub_average_sq_le_addCircle` restates the inequality for a function on
`AddCircle T` with the integral `volume` (total mass `T`), through its lift to `ℝ`.

Dividing by `T = √N` gives the bound
`Var h ≤ N (4π²)⁻¹ ∫ |h'|²` for the uniform law on a circle of length `√N`,
where `Var` is the variance under that law.
-/

public section

open MeasureTheory Set intervalIntegral
open scoped Real

namespace Riesz1

/-- A continuous function `ℝ → ℂ` is square integrable on each interval `(0, T]`. -/
lemma memLp_two_Ioc_of_continuous {g : ℝ → ℂ} (hg : Continuous g) (T : ℝ) :
    MemLp g 2 (volume.restrict (Ioc 0 T)) := by
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc (a := 0) (b := T)).exists_bound_of_continuousOn hg.continuousOn
  exact MemLp.of_bound hg.aestronglyMeasurable C
    ((ae_restrict_mem measurableSet_Ioc).mono fun x hx => hC x (Ioc_subset_Icc_self hx))

/-- Let `g` have derivative `g'` everywhere, with `g'` continuous and `g T = g 0`. For `n ≠ 0`,
the `n`-th Fourier coefficient of `g` on `[0, T]` equals `T / (2π i n)` times that of `g'`. -/
lemma fourierCoeffOn_eq_mul_fourierCoeffOn_deriv {T : ℝ} (hT : 0 < T) {g g' : ℝ → ℂ}
    (hg : ∀ x, HasDerivAt g (g' x) x) (hg' : Continuous g') (hper : g T = g 0) (n : ℤ)
    (hn : n ≠ 0) :
    fourierCoeffOn hT g n = (T / (2 * Real.pi * Complex.I * n)) * fourierCoeffOn hT g' n := by
  have h := fourierCoeffOn_of_hasDerivAt hT hn (fun x _ => hg x) (hg'.intervalIntegrable 0 T)
  have h0 : ((0 : ℝ) : AddCircle (T - 0)) = 0 := by simp
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [h, hper, sub_self, h0, fourier_eval_zero, one_mul, Complex.ofReal_zero, sub_zero]
  field_simp
  ring

/-- Comparison of one Fourier coefficient: for `n ≠ 0`, the squared modulus of the `n`-th
coefficient of `g` is at most `(T / 2π)²` times that of `g'`. -/
lemma norm_sq_fourierCoeffOn_le_of_hasDerivAt {T : ℝ} (hT : 0 < T) {g g' : ℝ → ℂ}
    (hg : ∀ x, HasDerivAt g (g' x) x) (hg' : Continuous g') (hper : g T = g 0) (n : ℤ)
    (hn : n ≠ 0) :
    ‖fourierCoeffOn hT g n‖ ^ 2 ≤
      (T / (2 * Real.pi)) ^ 2 * ‖fourierCoeffOn hT g' n‖ ^ 2 := by
  have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    have : (1 : ℤ) ≤ |n| := Int.one_le_abs hn
    exact_mod_cast this
  have hnorm :
      ‖(T : ℂ) / (2 * Real.pi * Complex.I * n)‖ = T / (2 * Real.pi * |(n : ℝ)|) := by
    simp [abs_of_pos hT, abs_of_pos Real.pi_pos]
  have h2 : 2 * Real.pi ≤ 2 * Real.pi * |(n : ℝ)| := le_mul_of_one_le_right (by positivity) hn1
  have hc : T / (2 * Real.pi * |(n : ℝ)|) ≤ T / (2 * Real.pi) :=
    div_le_div_of_nonneg_left hT.le (by positivity) h2
  rw [fourierCoeffOn_eq_mul_fourierCoeffOn_deriv hT hg hg' hper n hn, norm_mul, mul_pow, hnorm]
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  exact pow_le_pow_left₀ (by positivity) hc 2

/-- The zeroth Fourier coefficient of `x ↦ f x - m` vanishes when `T * m = ∫₀ᵀ f`. -/
lemma fourierCoeffOn_zero_sub_const {T : ℝ} (hT : 0 < T) {f : ℝ → ℝ} (hfc : Continuous f)
    (m : ℝ) (hm : T * m = ∫ y in (0 : ℝ)..T, f y) :
    fourierCoeffOn hT (fun x : ℝ => ((f x - m : ℝ) : ℂ)) 0 = 0 := by
  rw [fourierCoeffOn_eq_integral _ _ hT]
  simp only [neg_zero, fourier_zero, one_smul]
  rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_sub (hfc.intervalIntegrable 0 T)
    intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul, sub_zero, hm,
    sub_self, Complex.ofReal_zero, smul_zero]

/-- **Poincaré inequality on a circle.** For a `C^1` function `f : ℝ → ℝ` of period `T > 0`,
the integral of the squared deviation from the mean over `[0, T]` is at most `(T / 2π)²` times
the integral of `(f')²` over `[0, T]`. -/
theorem integral_sub_average_sq_le (T : ℝ) (hT : 0 < T) (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hper : Function.Periodic f T) :
    ∫ x in (0 : ℝ)..T, (f x - T⁻¹ * ∫ y in (0 : ℝ)..T, f y) ^ 2 ≤
      (T / (2 * Real.pi)) ^ 2 * ∫ x in (0 : ℝ)..T, (deriv f x) ^ 2 := by
  have hfc : Continuous f := hf.continuous
  have hdc : Continuous (deriv f) := hf.continuous_deriv (by norm_num)
  have hd : ∀ x, HasDerivAt f (deriv f x) x := fun x =>
    ((hf.differentiable (by norm_num)) x).hasDerivAt
  have hfT : f T = f 0 := by simpa using hper 0
  -- The mean `m` of `f` over `[0, T]`, with `T * m = ∫ f`.
  obtain ⟨m, hm_def⟩ : ∃ m : ℝ, m = T⁻¹ * ∫ y in (0 : ℝ)..T, f y := ⟨_, rfl⟩
  have hm : T * m = ∫ y in (0 : ℝ)..T, f y := by
    rw [hm_def, ← mul_assoc, mul_inv_cancel₀ hT.ne', one_mul]
  rw [← hm_def]
  -- Complex-valued centred function `F` and its derivative `G` on `[0, T]`.
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℂ, F = fun x => ((f x - m : ℝ) : ℂ) := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℂ, G = fun x => ((deriv f x : ℝ) : ℂ) := ⟨_, rfl⟩
  have hFd : ∀ x, HasDerivAt F (G x) x := by
    intro x
    rw [hF, hG]
    exact ((hd x).sub_const m).ofReal_comp
  have hFc : Continuous F := by
    rw [hF]
    exact Complex.continuous_ofReal.comp (hfc.sub continuous_const)
  have hGc : Continuous G := by
    rw [hG]
    exact Complex.continuous_ofReal.comp hdc
  have hFper : F T = F 0 := by
    rw [hF]
    simp only [hfT]
  -- Termwise comparison of the Fourier coefficients of `F` and `G`.
  have hterm : ∀ n : ℤ, ‖fourierCoeffOn hT F n‖ ^ 2 ≤
      (T / (2 * Real.pi)) ^ 2 * ‖fourierCoeffOn hT G n‖ ^ 2 := by
    intro n
    by_cases hn : n = 0
    · subst hn
      rw [hF, fourierCoeffOn_zero_sub_const hT hfc m hm, norm_zero, zero_pow two_ne_zero]
      positivity
    · exact norm_sq_fourierCoeffOn_le_of_hasDerivAt hT hFd hGc hFper n hn
  -- Parseval for `F` and `G`, then comparison of the two sums.
  have hsumF := hasSum_sq_fourierCoeffOn hT (memLp_two_Ioc_of_continuous hFc T)
  have hsumG := (hasSum_sq_fourierCoeffOn hT (memLp_two_Ioc_of_continuous hGc T)).mul_left
    ((T / (2 * Real.pi)) ^ 2)
  have hle := hasSum_le hterm hsumF hsumG
  have hnF : ∀ x, ‖F x‖ ^ 2 = (f x - m) ^ 2 := by
    intro x
    rw [hF]
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hnG : ∀ x, ‖G x‖ ^ 2 = (deriv f x) ^ 2 := by
    intro x
    rw [hG]
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp only [hnF, hnG, sub_zero, smul_eq_mul] at hle
  have hA : T * (T⁻¹ * ∫ x in (0 : ℝ)..T, (f x - m) ^ 2) =
      ∫ x in (0 : ℝ)..T, (f x - m) ^ 2 :=
    mul_inv_cancel_left₀ hT.ne' _
  have hB : T * ((T / (2 * Real.pi)) ^ 2 * (T⁻¹ * ∫ x in (0 : ℝ)..T, (deriv f x) ^ 2)) =
      (T / (2 * Real.pi)) ^ 2 * ∫ x in (0 : ℝ)..T, (deriv f x) ^ 2 := by
    rw [mul_left_comm, mul_inv_cancel_left₀ hT.ne']
  have key := mul_le_mul_of_nonneg_left hle hT.le
  rwa [hA, hB] at key

/-- **Poincaré inequality on `AddCircle T`.** Let `f : AddCircle T → ℝ` have a `C^1` lift
`x ↦ f x` to `ℝ`. Then the integral of the squared deviation of `f` from its mean, for the Haar
integral `volume` of total mass `T`, is at most `(T / 2π)²` times the integral of `(f')²` of the
lift over `[0, T]`. -/
theorem integral_sub_average_sq_le_addCircle (T : ℝ) [hT : Fact (0 < T)] (f : AddCircle T → ℝ)
    (hf : ContDiff ℝ 1 fun x : ℝ => f (x : AddCircle T)) :
    ∫ t : AddCircle T, (f t - T⁻¹ * ∫ s : AddCircle T, f s) ^ 2 ≤
      (T / (2 * Real.pi)) ^ 2 *
        ∫ x in (0 : ℝ)..T, (deriv (fun y : ℝ => f (y : AddCircle T)) x) ^ 2 := by
  have hint : ∀ g : AddCircle T → ℝ,
      ∫ t : AddCircle T, g t = ∫ x in (0 : ℝ)..T, g (x : AddCircle T) := by
    intro g
    rw [← AddCircle.intervalIntegral_preimage T 0 g, zero_add]
  have hper : Function.Periodic (fun x : ℝ => f (x : AddCircle T)) T := by
    intro x
    simp only [AddCircle.coe_add_period]
  have hsq : ∫ t : AddCircle T, (f t - T⁻¹ * ∫ s : AddCircle T, f s) ^ 2 =
      ∫ x in (0 : ℝ)..T,
        (f (x : AddCircle T) - T⁻¹ * ∫ y in (0 : ℝ)..T, f (y : AddCircle T)) ^ 2 := by
    rw [hint (fun t => (f t - T⁻¹ * ∫ s : AddCircle T, f s) ^ 2), hint f]
  rw [hsq]
  exact integral_sub_average_sq_le T hT.out (fun x : ℝ => f (x : AddCircle T)) hf hper

end Riesz1
