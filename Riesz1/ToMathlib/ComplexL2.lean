/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Real and imaginary parts in L²

Continuous coordinate maps, reconstruction, and the complex inner
product in real coordinates. These apply to every measure.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace Riesz1

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

/-- The real part of a complex L² class. -/
def complexL2Re : Lp ℂ 2 μ →L[ℝ] Lp ℝ 2 μ := Complex.reCLM.compLpL 2 μ

/-- The imaginary part of a complex L² class. -/
def complexL2Im : Lp ℂ 2 μ →L[ℝ] Lp ℝ 2 μ := Complex.imCLM.compLpL 2 μ

/-- A real L² class as a complex L² class. -/
def realL2Complex : Lp ℝ 2 μ →L[ℝ] Lp ℂ 2 μ := Complex.ofRealCLM.compLpL 2 μ

theorem complexL2Re_ae (f : Lp ℂ 2 μ) :
    (complexL2Re μ f : Ω → ℝ) =ᵐ[μ] fun x => (f x).re :=
  ContinuousLinearMap.coeFn_compLpL Complex.reCLM f

theorem complexL2Im_ae (f : Lp ℂ 2 μ) :
    (complexL2Im μ f : Ω → ℝ) =ᵐ[μ] fun x => (f x).im :=
  ContinuousLinearMap.coeFn_compLpL Complex.imCLM f

theorem realL2Complex_ae (f : Lp ℝ 2 μ) :
    (realL2Complex μ f : Ω → ℂ) =ᵐ[μ] fun x => (f x : ℂ) :=
  ContinuousLinearMap.coeFn_compLpL Complex.ofRealCLM f

theorem complexL2_ext {f g : Lp ℂ 2 μ}
    (hr : complexL2Re μ f = complexL2Re μ g) (hi : complexL2Im μ f = complexL2Im μ g) : f = g := by
  apply Lp.ext
  have hr' := Lp.ext_iff.mp hr
  have hi' := Lp.ext_iff.mp hi
  filter_upwards [hr', hi', complexL2Re_ae μ f, complexL2Re_ae μ g,
    complexL2Im_ae μ f, complexL2Im_ae μ g] with x hrx hix hrf hrg hif hig
  exact Complex.ext (hrf.symm.trans (hrx.trans hrg)) (hif.symm.trans (hix.trans hig))

theorem complexL2Re_smul (z : ℂ) (f : Lp ℂ 2 μ) :
    complexL2Re μ (z • f) = z.re • complexL2Re μ f - z.im • complexL2Im μ f := by
  apply Lp.ext
  filter_upwards [complexL2Re_ae μ (z • f), complexL2Re_ae μ f, complexL2Im_ae μ f,
    Lp.coeFn_smul z f, Lp.coeFn_sub (z.re • complexL2Re μ f) (z.im • complexL2Im μ f),
    Lp.coeFn_smul z.re (complexL2Re μ f), Lp.coeFn_smul z.im (complexL2Im μ f)]
      with x hz hr hi hzf hs h₁ h₂
  rw [hz, hs, hzf]
  simp only [Pi.sub_apply]
  rw [h₁, h₂]
  simp only [Pi.smul_apply, smul_eq_mul, Complex.mul_re, hr, hi]

theorem complexL2Im_smul (z : ℂ) (f : Lp ℂ 2 μ) :
    complexL2Im μ (z • f) = z.re • complexL2Im μ f + z.im • complexL2Re μ f := by
  apply Lp.ext
  filter_upwards [complexL2Im_ae μ (z • f), complexL2Re_ae μ f, complexL2Im_ae μ f,
    Lp.coeFn_smul z f, Lp.coeFn_add (z.re • complexL2Im μ f) (z.im • complexL2Re μ f),
    Lp.coeFn_smul z.re (complexL2Im μ f), Lp.coeFn_smul z.im (complexL2Re μ f)]
      with x hz hr hi hzf hs h₁ h₂
  rw [hz, hs, hzf]
  simp only [Pi.add_apply]
  rw [h₁, h₂]
  simp only [Pi.smul_apply, smul_eq_mul, Complex.mul_im, hr, hi]

theorem complexL2Re_ofReal (f : Lp ℝ 2 μ) : complexL2Re μ (realL2Complex μ f) = f := by
  apply Lp.ext
  filter_upwards [complexL2Re_ae μ (realL2Complex μ f), realL2Complex_ae μ f] with x h₁ h₂
  rw [h₁, h₂, Complex.ofReal_re]

theorem complexL2Im_ofReal (f : Lp ℝ 2 μ) : complexL2Im μ (realL2Complex μ f) = 0 := by
  apply Lp.ext
  filter_upwards [complexL2Im_ae μ (realL2Complex μ f), realL2Complex_ae μ f,
    Lp.coeFn_zero ℝ 2 μ] with x h₁ h₂ h₀
  rw [h₁, h₂, h₀, Complex.ofReal_im]
  rfl

/-- Continuous reconstruction from real and imaginary coordinates. -/
def complexL2OfPair : (Lp ℝ 2 μ × Lp ℝ 2 μ) →L[ℝ] Lp ℂ 2 μ :=
  (realL2Complex μ).comp (ContinuousLinearMap.fst ℝ _ _) +
    Complex.I • (realL2Complex μ).comp (ContinuousLinearMap.snd ℝ _ _)

theorem complexL2OfPair_ae (f g : Lp ℝ 2 μ) :
    (complexL2OfPair μ (f, g) : Ω → ℂ) =ᵐ[μ] fun x => (f x : ℂ) + Complex.I * (g x : ℂ) := by
  filter_upwards [Lp.coeFn_add (realL2Complex μ f) (Complex.I • realL2Complex μ g),
    Lp.coeFn_smul Complex.I (realL2Complex μ g), realL2Complex_ae μ f, realL2Complex_ae μ g]
      with x hadd hsmul hf hg
  change (realL2Complex μ f + Complex.I • realL2Complex μ g) x = _
  rw [hadd]
  simp only [Pi.add_apply]
  rw [hsmul]
  simp only [Pi.smul_apply, smul_eq_mul, hf, hg]

theorem complexL2Re_ofPair (p : Lp ℝ 2 μ × Lp ℝ 2 μ) :
    complexL2Re μ (complexL2OfPair μ p) = p.1 := by
  change complexL2Re μ (realL2Complex μ p.1 + Complex.I • realL2Complex μ p.2) = _
  rw [map_add, complexL2Re_smul, complexL2Re_ofReal, complexL2Re_ofReal, complexL2Im_ofReal]
  simp

theorem complexL2Im_ofPair (p : Lp ℝ 2 μ × Lp ℝ 2 μ) :
    complexL2Im μ (complexL2OfPair μ p) = p.2 := by
  change complexL2Im μ (realL2Complex μ p.1 + Complex.I • realL2Complex μ p.2) = _
  rw [map_add, complexL2Im_smul, complexL2Re_ofReal, complexL2Im_ofReal, complexL2Im_ofReal]
  simp

theorem complexL2OfPair_re_im (f : Lp ℂ 2 μ) :
    complexL2OfPair μ (complexL2Re μ f, complexL2Im μ f) = f :=
  complexL2_ext μ (complexL2Re_ofPair μ _) (complexL2Im_ofPair μ _)

theorem complexL2_inner_re (f g : Lp ℂ 2 μ) :
    (inner ℂ f g).re = inner ℝ (complexL2Re μ f) (complexL2Re μ g) +
      inner ℝ (complexL2Im μ f) (complexL2Im μ g) := by
  change RCLike.re (inner ℂ f g) = _
  rw [L2.inner_def, ← integral_re (L2.integrable_inner (𝕜 := ℂ) f g)]
  rw [L2.inner_def, L2.inner_def, ← integral_add (L2.integrable_inner _ _) (L2.integrable_inner _ _)]
  apply integral_congr_ae
  filter_upwards [complexL2Re_ae μ f, complexL2Re_ae μ g, complexL2Im_ae μ f,
    complexL2Im_ae μ g] with x hrf hrg hif hig
  simp [hrf, hrg, hif, hig, RCLike.inner_apply, RCLike.re_to_complex]


theorem complexL2_inner_im (f g : Lp ℂ 2 μ) :
    (inner ℂ f g).im = inner ℝ (complexL2Re μ f) (complexL2Im μ g) -
      inner ℝ (complexL2Im μ f) (complexL2Re μ g) := by
  change RCLike.im (inner ℂ f g) = _
  rw [L2.inner_def, ← integral_im (L2.integrable_inner (𝕜 := ℂ) f g)]
  rw [L2.inner_def, L2.inner_def, ← integral_sub (L2.integrable_inner _ _) (L2.integrable_inner _ _)]
  apply integral_congr_ae
  filter_upwards [complexL2Re_ae μ f, complexL2Re_ae μ g, complexL2Im_ae μ f,
    complexL2Im_ae μ g] with x hrf hrg hif hig
  simp [hrf, hrg, hif, hig, RCLike.inner_apply, RCLike.im_to_complex]
  ring

end Riesz1
