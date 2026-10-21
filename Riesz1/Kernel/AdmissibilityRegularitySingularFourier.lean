/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.AdmissibilityRegularityPrimitive
public import Riesz1.Kernel.SeminormScalingKernel
public import Mathlib.MeasureTheory.Integral.Prod
/-!
# Fourier multiplier of the Hölder singular integral

Fubini identifies the absolutely convergent singular integral
with its Fourier multiplier on a circle of arbitrary length. Averaging the translations
`u` and `-u` cancels the imaginary part. The scalar multiplier is then computed by the
Lévy scaling integral. The auxiliary statements are internal.
-/

public section

open MeasureTheory
open scoped ComplexConjugate
namespace Riesz1.Internal
variable {T : ℝ} [Fact (0 < T)]
/-- Translation multiplies a Fourier coefficient by the corresponding character. -/
lemma fourierCoeff_translate_sub (f : AddCircle T → ℂ) (y : AddCircle T) (k : ℤ) :
    fourierCoeff (fun x => f (x - y)) k = fourier (-k) y * fourierCoeff f k := by
  unfold fourierCoeff
  simp only [smul_eq_mul]
  have hs := integral_add_right_eq_self (μ := AddCircle.haarAddCircle)
    (fun x => fourier (-k) x * f (x - y)) y
  rw [← hs]
  simp only [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul, add_sub_cancel_right]
  rw [← integral_const_mul]
  congr 1
  funext x
  ring
omit [Fact (0 < T)] in
/-- Reflection conjugates a Fourier character. -/
lemma fourier_neg_arg (k : ℤ) (u : AddCircle T) :
    fourier (-k) (-u) = conj (fourier (-k) u) := by
  simp only [fourier_apply, smul_neg, AddCircle.toCircle_neg, Circle.coe_inv_eq_conj]
omit [Fact (0 < T)] in
/-- The sum of a character at opposite real arguments is twice a cosine. -/
lemma fourier_add_neg_eq_cos (k : ℤ) (u : ℝ) :
    fourier (-k) (u : AddCircle T) + fourier (-k) (-u : AddCircle T) =
      (2 * Real.cos (2 * Real.pi * ((k : ℝ) / T * u)) : ℝ) := by
  rw [fourier_neg_arg, Complex.add_conj]
  congr 1
  rw [fourier_coe_apply]
  have he : 2 * (Real.pi : ℂ) * Complex.I * ((-k : ℤ) : ℂ) * (u : ℂ) / (T : ℂ) =
      ((-(2 * Real.pi * ((k : ℝ) / T * u)) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [he, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
/-- Fourier multiplier of the absolutely convergent singular integral. -/
lemma fourierCoeff_holder_singular_integral {τ r B : ℝ} (hτ : 0 < τ) (hr : τ < r)
    (hB : 0 ≤ B) (f : AddCircle T → ℝ) (hf : Continuous f)
    (hsmall : ∀ (x : AddCircle T) (u : ℝ), |f x - f (x - (u : AddCircle T))| ≤ B * |u| ^ r)
    (hlarge : ∀ (x : AddCircle T) (u : ℝ), |f x - f (x - (u : AddCircle T))| ≤ 2 * B) (k : ℤ) :
    fourierCoeff (fun x => ((∫ u : ℝ, (f x - f (x - (u : AddCircle T))) *
      |u| ^ (-(1 + τ)) : ℝ) : ℂ)) k =
        ((|((k : ℝ) / T)| ^ τ * levyIntegral τ : ℝ) : ℂ) *
          fourierCoeff (fun x => (f x : ℂ)) k := by
  let R : AddCircle T → ℝ → ℝ := fun x u =>
    (f x - f (x - (u : AddCircle T))) * |u| ^ (-(1 + τ))
  let G : AddCircle T → ℝ → ℂ := fun x u => fourier (-k) x * (R x u : ℂ)
  have hfm : Continuous (fun p : AddCircle T × ℝ => f p.1 - f (p.1 - (p.2 : AddCircle T))) :=
    (hf.comp continuous_fst).sub (hf.comp (continuous_fst.sub
      ((AddCircle.continuous_mk' T).comp continuous_snd)))
  have hgm : Measurable (Function.uncurry G) := by
    exact ((fourier (-k)).continuous.comp continuous_fst).measurable.mul
      (Complex.continuous_ofReal.measurable.comp (hfm.measurable.mul
        ((continuous_abs.measurable.comp measurable_snd).pow_const _)))
  have hint : Integrable (Function.uncurry G) (AddCircle.haarAddCircle.prod volume) := by
    refine Integrable.mono'
      ((integrable_holderSingularEnvelope (B := B) hτ hr).comp_snd AddCircle.haarAddCircle)
      hgm.aestronglyMeasurable (ae_of_all _ fun p => ?_)
    change ‖fourier (-k) p.1 * (R p.1 p.2 : ℂ)‖ ≤ _
    rw [norm_mul, fourier_apply, Circle.norm_coe, one_mul, Complex.norm_real]
    by_cases hu : p.2 = 0
    · simp only [R, hu, AddCircle.coe_zero, sub_zero, sub_self, zero_mul, norm_zero]
      exact holderSingularEnvelope_nonneg hB _
    · exact norm_singular_residual_le_envelope hτ hB (hsmall p.1 p.2) (hlarge p.1 p.2) hu
  have hinner (u : ℝ) : ∫ x : AddCircle T, G x u ∂AddCircle.haarAddCircle =
      (1 - fourier (-k) (u : AddCircle T)) *
        fourierCoeff (fun x => (f x : ℂ)) k * (|u| ^ (-(1 + τ)) : ℝ) := by
    have hfc : Continuous (fun x => (f x : ℂ)) := Complex.continuous_ofReal.comp hf
    have hfi : Integrable (fun x => (f x : ℂ)) AddCircle.haarAddCircle := by
      simpa only [MeasureTheory.IntegrableOn, Measure.restrict_univ, Function.comp_def, Pi.sub_apply, id_eq] using
        (ContinuousOn.integrableOn_compact (μ := AddCircle.haarAddCircle)
          isCompact_univ hfc.continuousOn)
    have hfshift : Integrable (fun x => (f (x - (u : AddCircle T)) : ℂ))
        AddCircle.haarAddCircle := by
      simpa only [MeasureTheory.IntegrableOn, Measure.restrict_univ, Function.comp_def, Pi.sub_apply, id_eq] using
        (ContinuousOn.integrableOn_compact (μ := AddCircle.haarAddCircle)
          isCompact_univ (hfc.comp (continuous_id.sub continuous_const)).continuousOn)
    have h1 : Integrable (fun x : AddCircle T => fourier (-k) x * (f x : ℂ))
        AddCircle.haarAddCircle := hfi.fourier_smul (-k)
    have h2 : Integrable (fun x : AddCircle T => fourier (-k) x * (f (x - (u : AddCircle T)) : ℂ))
        AddCircle.haarAddCircle :=
      hfshift.fourier_smul (-k)
    have he (x : AddCircle T) : G x u =
        (fourier (-k) x * (f x : ℂ) - fourier (-k) x * (f (x - (u : AddCircle T)) : ℂ)) *
          (|u| ^ (-(1 + τ)) : ℝ) := by
      dsimp [G, R]
      push_cast
      ring
    simp_rw [he]
    rw [integral_mul_const, integral_sub h1 h2]
    change (fourierCoeff (fun x => (f x : ℂ)) k -
      fourierCoeff (fun x => (f (x - (u : AddCircle T)) : ℂ)) k) * _ = _
    rw [fourierCoeff_translate_sub (fun x => (f x : ℂ)) (u : AddCircle T) k]
    ring
  have hswap : fourierCoeff (fun x => ((∫ u : ℝ, R x u : ℝ) : ℂ)) k =
      ∫ u : ℝ, ∫ x : AddCircle T, G x u ∂AddCircle.haarAddCircle := by
    unfold fourierCoeff
    simp only [smul_eq_mul]
    have he (x : AddCircle T) : fourier (-k) x * ((∫ u : ℝ, R x u : ℝ) : ℂ) = ∫ u, G x u := by
      rw [← integral_complex_ofReal, integral_const_mul]
    simp_rw [he]
    exact integral_integral_swap hint
  let H : ℝ → ℂ := fun u => ∫ x : AddCircle T, G x u ∂AddCircle.haarAddCircle
  have hH : Integrable H := hint.integral_prod_right
  have havg : ∫ u, H u = (1 / 2 : ℂ) * ∫ u, H u + H (-u) := by
    rw [integral_add hH hH.comp_neg, integral_neg_eq_self H volume]
    ring
  have hpair (u : ℝ) : H u + H (-u) =
      (2 : ℂ) * (((1 - Real.cos (2 * Real.pi * ((k : ℝ) / T * u))) *
        |u| ^ (-(1 + τ)) : ℝ) : ℂ) * fourierCoeff (fun x => (f x : ℂ)) k := by
    dsimp [H]
    rw [hinner u, hinner (-u)]
    simp only [abs_neg, AddCircle.coe_neg]
    have hcos := fourier_add_neg_eq_cos (T := T) k u
    simp only [Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_ofNat] at hcos ⊢
    linear_combination -(fourierCoeff (fun x => (f x : ℂ)) k *
      ((|u| ^ (-(1 + τ)) : ℝ) : ℂ)) * hcos
  rw [hswap]
  change ∫ u, H u = _
  rw [havg]
  simp_rw [hpair]
  rw [integral_mul_const, integral_const_mul, integral_complex_ofReal]
  have he : ∫ u : ℝ, (1 - Real.cos (2 * Real.pi * ((k : ℝ) / T * u))) *
      |u| ^ (-(1 + τ)) = |((k : ℝ) / T)| ^ τ * levyIntegral τ := by
    simp_rw [Real.rpow_neg (abs_nonneg _), ← div_eq_mul_inv]
    exact integral_levy_scale hτ _
  rw [he]
  ring
end Riesz1.Internal
