/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Distribution.TemperedDistribution
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Line Fourier transform of integrable square-integrable functions

For a function that is both integrable and square integrable on the line, the
`L²` Fourier transform agrees almost everywhere with the classical integral
`∫ g(x) e^{-2πiηx} dx`. The proof pairs both transforms with smooth compactly
supported test functions, using the duality of the tempered distribution
Fourier transform and the multiplication formula for integrable functions.
-/

public section

open MeasureTheory FourierTransform SchwartzMap
open scoped ComplexInnerProductSpace SchwartzMap ContDiff

namespace Riesz1

/-- The Fourier transform on the line, written as a Fourier integral with the
standard character and the inner product pairing. -/
private lemma fourier_eq_fourierIntegral (f : ℝ → ℂ) (w : ℝ) :
    𝓕 f w = VectorFourier.fourierIntegral Real.fourierChar (volume : Measure ℝ)
      (innerₗ ℝ) f w := by
  rw [Real.fourier_eq]
  simp [VectorFourier.fourierIntegral]

/-- Multiplication formula between a Schwartz function and an integrable function. -/
private lemma integral_fourier_mul_schwartz_integrable (ψ : 𝓢(ℝ, ℂ)) {g : ℝ → ℂ}
    (hg : Integrable g) :
    ∫ η, 𝓕 (ψ : ℝ → ℂ) η * g η = ∫ x, (ψ : ℝ → ℂ) x * 𝓕 g x := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (μ := volume) (ν := volume)
    (L := innerₗ ℝ) (e := Real.fourierChar) (f := (ψ : ℝ → ℂ)) (g := g)
    Real.continuous_fourierChar (by fun_prop) ψ.integrable hg
  simp only [smul_eq_mul] at h
  simp only [fourier_eq_fourierIntegral]
  simpa [real_inner_comm] using h

/-- Pairing the `L²` Fourier transform with a Schwartz function and the
integrable Fourier transform agree, for an element both integrable and `L²`. -/
private lemma integral_fourier_toLp_mul_schwartz {g : ℝ → ℂ} (hg1 : Integrable g)
    (hg2 : MemLp g 2 volume) (ψ : 𝓢(ℝ, ℂ)) :
    ∫ η, ψ η * ((𝓕 (hg2.toLp g) : Lp ℂ 2 volume) : ℝ → ℂ) η = ∫ η, ψ η * 𝓕 g η := by
  have hL := congrArg (fun T : TemperedDistribution ℝ ℂ => T (ψ : 𝓢(ℝ, ℂ)))
    (Lp.fourier_toTemperedDistribution_eq (hg2.toLp g))
  simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply,
    smul_eq_mul, SchwartzMap.fourier_coe] at hL
  have hmul := integral_fourier_mul_schwartz_integrable ψ hg1
  have hae : ∫ x, 𝓕 (ψ : ℝ → ℂ) x * ((hg2.toLp g : Lp ℂ 2 volume) : ℝ → ℂ) x =
      ∫ x, 𝓕 (ψ : ℝ → ℂ) x * g x := by
    apply integral_congr_ae
    filter_upwards [hg2.coeFn_toLp] with x hx
    rw [hx]
  rw [← hL, hae, hmul]

/-- The `L²` Fourier transform of an integrable square-integrable function agrees
almost everywhere with the classical Fourier integral. -/
theorem fourier_toLp_ae {g : ℝ → ℂ} (hg1 : Integrable g) (hg2 : MemLp g 2 volume) :
    ((𝓕 (hg2.toLp g) : Lp ℂ 2 volume) : ℝ → ℂ) =ᵐ[volume] 𝓕 g := by
  set A : ℝ → ℂ := ((𝓕 (hg2.toLp g) : Lp ℂ 2 volume) : ℝ → ℂ) with hA_def
  have hAloc : LocallyIntegrable A volume := (Lp.memLp _).locallyIntegrable one_le_two
  have hBcont : Continuous (𝓕 g) := VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (innerSL ℝ).continuous₂ hg1
  have hloc : LocallyIntegrable (fun x => A x - 𝓕 g x) volume :=
    hAloc.sub hBcont.locallyIntegrable
  have hkey : ∀ h : ℝ → ℝ, ContDiff ℝ ∞ h → HasCompactSupport h →
      ∫ x, h x • (A x - 𝓕 g x) = 0 := by
    intro h hh hc
    have hcc : HasCompactSupport (fun x : ℝ => (h x : ℂ)) :=
      hc.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
    have hsm : ContDiff ℝ ∞ (fun x : ℝ => (h x : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp hh
    have hψ : ∫ η, (h η : ℂ) * A η = ∫ η, (h η : ℂ) * 𝓕 g η :=
      integral_fourier_toLp_mul_schwartz hg1 hg2 (hcc.toSchwartzMap hsm)
    have hint1 : Integrable (fun x => h x • A x) volume :=
      hAloc.integrable_smul_left_of_hasCompactSupport hh.continuous hc
    have hint2 : Integrable (fun x => h x • 𝓕 g x) volume :=
      (hBcont.locallyIntegrable).integrable_smul_left_of_hasCompactSupport hh.continuous hc
    have e1 : (fun x => h x • (A x - 𝓕 g x)) =
        fun x => h x • A x - h x • 𝓕 g x := by
      funext x
      rw [smul_sub]
    rw [e1, integral_sub hint1 hint2, sub_eq_zero]
    simp only [Complex.real_smul]
    exact hψ
  filter_upwards [ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc hkey] with x hx
  exact sub_eq_zero.mp hx

/-- The squared norm of an `L²` element is the integral of the squared pointwise norm. -/
private lemma norm_sq_eq_integral_Lp (F : Lp ℂ 2 volume) :
    ‖F‖ ^ 2 = ∫ a, ‖(F : ℝ → ℂ) a‖ ^ 2 := by
  have h1 : inner ℂ F F = ∫ a, inner ℂ ((F : ℝ → ℂ) a) ((F : ℝ → ℂ) a) := L2.inner_def F F
  have h2 : inner ℂ F F = ((‖F‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]; rfl
  have h3 : ∀ a, inner ℂ ((F : ℝ → ℂ) a) ((F : ℝ → ℂ) a) =
      ((‖(F : ℝ → ℂ) a‖ ^ 2 : ℝ) : ℂ) := fun a => by
    rw [inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]; rfl
  simp only [h3] at h1
  rw [integral_complex_ofReal, h2] at h1
  exact_mod_cast h1

/-- Plancherel's identity for functions that are integrable and square integrable. -/
theorem integral_norm_sq_fourier {g : ℝ → ℂ} (hg1 : Integrable g) (hg2 : MemLp g 2 volume) :
    ∫ η, ‖𝓕 g η‖ ^ 2 = ∫ x, ‖g x‖ ^ 2 := by
  have hP : ‖𝓕 (hg2.toLp g)‖ = ‖hg2.toLp g‖ := Lp.norm_fourier_eq _
  have hL : ∫ η, ‖𝓕 g η‖ ^ 2 = ∫ η, ‖((𝓕 (hg2.toLp g) : Lp ℂ 2 volume) : ℝ → ℂ) η‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [fourier_toLp_ae hg1 hg2] with η hη
    rw [hη]
  have hR : ∫ x, ‖g x‖ ^ 2 = ∫ x, ‖((hg2.toLp g : Lp ℂ 2 volume) : ℝ → ℂ) x‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [hg2.coeFn_toLp] with x hx
    rw [hx]
  rw [hL, hR, ← norm_sq_eq_integral_Lp, ← norm_sq_eq_integral_Lp, hP]

/-- The real inner product on the line is the product. -/
private lemma inner_real_eq_mul (a b : ℝ) : inner ℝ a b = a * b := by
  simp [mul_comm]

/-- Translation of the integral Fourier transform: the transform of `x ↦ g (x + u) - g x`
is the transform of `g` multiplied by `e^{2πiηu} - 1`. -/
theorem fourier_translate_sub {g : ℝ → ℂ} (hg : Integrable g) (u η : ℝ) :
    𝓕 (fun x => g (x + u) - g x) η =
      (((Real.fourierChar (η * u) : Circle) : ℂ) - 1) * 𝓕 g η := by
  have hpt : ∀ w : ℝ, ((Real.fourierChar (-(inner ℝ (w - u) η)) : Circle) : ℂ) =
      ((Real.fourierChar (η * u) : Circle) : ℂ) *
        ((Real.fourierChar (-(inner ℝ w η)) : Circle) : ℂ) := by
    intro w
    rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]
    congr 2
    simp only [inner_sub_left, inner_real_eq_mul]
    ring
  have hA : Integrable (fun v : ℝ => ((Real.fourierChar (-(inner ℝ v η)) : Circle) : ℂ) * g (v + u)) := by
    have := (Real.fourierIntegral_convergent_iff η).2 (hg.comp_add_right u)
    simpa [Circle.smul_def, smul_eq_mul] using this
  have hB : Integrable (fun v : ℝ => ((Real.fourierChar (-(inner ℝ v η)) : Circle) : ℂ) * g v) := by
    have := (Real.fourierIntegral_convergent_iff η).2 hg
    simpa [Circle.smul_def, smul_eq_mul] using this
  have hshift : ∫ v, ((Real.fourierChar (-(inner ℝ v η)) : Circle) : ℂ) * g (v + u) =
      ∫ w, ((Real.fourierChar (-(inner ℝ (w - u) η)) : Circle) : ℂ) * g w := by
    rw [← integral_add_right_eq_self (fun w => ((Real.fourierChar (-(inner ℝ (w - u) η)) :
      Circle) : ℂ) * g w) u]
    simp only [add_sub_cancel_right]
  rw [Real.fourier_eq, Real.fourier_eq]
  simp only [Circle.smul_def, smul_eq_mul, smul_sub]
  rw [integral_sub hA hB, hshift]
  simp_rw [hpt, mul_assoc]
  rw [integral_const_mul, sub_mul, one_mul]

/-- The modulus of `e^{2πix} - 1` on the unit circle. -/
lemma norm_sq_fourierChar_sub_one (x : ℝ) :
    ‖((Real.fourierChar x : Circle) : ℂ) - 1‖ ^ 2 = 2 - 2 * Real.cos (2 * Real.pi * x) := by
  rw [Real.fourierChar_apply, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.one_re, Complex.one_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]
  linear_combination Real.sin_sq_add_cos_sq (2 * Real.pi * x)

/-- The cosine weighted line seminorm identity: the weight `1 - cos(2πηu)` pairs with
the squared modulus of the transform to give half the squared translation increment. -/
theorem integral_one_sub_cos_norm_sq_fourier {g : ℝ → ℂ} (hg1 : Integrable g)
    (hg2 : MemLp g 2 volume) (u : ℝ) :
    ∫ η, (1 - Real.cos (2 * Real.pi * (η * u))) * ‖𝓕 g η‖ ^ 2 =
      (1 / 2) * ∫ x, ‖g (x + u) - g x‖ ^ 2 := by
  have hh1 : Integrable (fun x => g (x + u) - g x) := (hg1.comp_add_right u).sub hg1
  have hgu : MemLp (fun x => g (x + u)) 2 volume :=
    hg2.comp_measurePreserving (measurePreserving_add_right volume u)
  have hh2 : MemLp (fun x => g (x + u) - g x) 2 volume := hgu.sub hg2
  have hkey : ∀ η : ℝ, ‖𝓕 (fun x => g (x + u) - g x) η‖ ^ 2 =
      2 * ((1 - Real.cos (2 * Real.pi * (η * u))) * ‖𝓕 g η‖ ^ 2) := by
    intro η
    rw [fourier_translate_sub hg1 u η, norm_mul, mul_pow, norm_sq_fourierChar_sub_one]
    ring
  have hsum := integral_norm_sq_fourier hh1 hh2
  simp_rw [hkey, integral_const_mul] at hsum
  linarith

/-- The squared modulus of the integral Fourier transform is integrable. -/
theorem integrable_norm_sq_fourier {g : ℝ → ℂ} (hg1 : Integrable g) (hg2 : MemLp g 2 volume) :
    Integrable (fun η : ℝ => ‖𝓕 g η‖ ^ 2) := by
  have h := (Lp.memLp (𝓕 (hg2.toLp g) : Lp ℂ 2 volume)).integrable_norm_pow (by norm_num)
  exact h.congr ((fourier_toLp_ae hg1 hg2).mono (fun η hη => by simp only [hη]))

end Riesz1
