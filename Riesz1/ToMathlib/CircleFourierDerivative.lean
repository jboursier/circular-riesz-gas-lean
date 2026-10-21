/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# Fourier coefficients of an integrable punctured derivative

For a continuous periodic function, differentiability off a countable set and an
integrable derivative suffice for integration by parts against every Fourier character.
In particular, no boundary atoms are lost at the exceptional points. This supplies the
derivative-to-transport coefficient bridge.
-/

public section

open MeasureTheory Set intervalIntegral

namespace Riesz1.CircleFourier

/-- Integration by parts against a unit-period character is valid across a countable
exceptional set when the derivative is integrable. The formula uses unnormalized
arclength on the left and normalized Haar coefficients on the right. -/
theorem integral_deriv_mul_fourier {T : ℝ} [hT : Fact (0 < T)]
    {f : AddCircle T → ℝ} (hf : Continuous f) {S : Set ℝ} (hS : S.Countable)
    (hd : ∀ x : ℝ, x ∉ S → DifferentiableAt ℝ (fun t : ℝ => f (t : AddCircle T)) x)
    (hi : IntervalIntegrable (deriv (fun t : ℝ => f (t : AddCircle T))) volume 0 T)
    (k : ℤ) :
    (∫ t in (0 : ℝ)..T, ((deriv (fun u : ℝ => f (u : AddCircle T)) t : ℝ) : ℂ) *
        fourier (-k) (t : AddCircle T)) =
      (T : ℂ) * (2 * Real.pi * Complex.I * (k : ℂ) / T) *
        fourierCoeff (fun x => (f x : ℂ)) k := by
  let F : ℝ → ℂ := fun t => (f (t : AddCircle T) : ℂ)
  let q : ℝ → ℂ := fun t => ((deriv (fun u : ℝ => f (u : AddCircle T)) t : ℝ) : ℂ)
  let χ : ℝ → ℂ := fun t => fourier (-k) (t : AddCircle T)
  let c : ℂ := -2 * Real.pi * Complex.I * (k : ℂ) / T
  have hF : Continuous F := Complex.continuous_ofReal.comp (hf.comp (AddCircle.continuous_mk' T))
  have hχ : Continuous χ := (map_continuous (fourier (-k))).comp (AddCircle.continuous_mk' T)
  have hχd : ∀ t : ℝ, HasDerivAt χ (c * χ t) t := hasDerivAt_fourier_neg T k
  have hq : IntervalIntegrable q volume 0 T :=
    ⟨Complex.ofRealCLM.integrable_comp hi.1, Complex.ofRealCLM.integrable_comp hi.2⟩
  have hprod : IntervalIntegrable (fun t => q t * χ t) volume 0 T :=
    hq.mul_continuousOn hχ.continuousOn
  have hFχ : IntervalIntegrable (fun t => F t * χ t) volume 0 T :=
    (hF.mul hχ).intervalIntegrable 0 T
  have hFTC := integral_eq_of_hasDerivAt_off_countable (fun t => F t * χ t)
    (fun t => q t * χ t + c * (F t * χ t)) hS (hF.mul hχ).continuousOn
    (fun t ht => by
      convert ((hd t ht.2).hasDerivAt.ofReal_comp).mul (hχd t) using 1
      dsimp [F, q]
      ring)
    (hprod.add (hFχ.const_mul c))
  have hend : F T * χ T - F 0 * χ 0 = 0 := by
    have hcoe : (T : AddCircle T) = 0 := by
      simp
    change (f (T : AddCircle T) : ℂ) * fourier (-k) (T : AddCircle T) -
      (f ((0 : ℝ) : AddCircle T) : ℂ) * fourier (-k) ((0 : ℝ) : AddCircle T) = 0
    rw [hcoe]
    simp only [AddCircle.coe_zero, sub_self]
  rw [hend, integral_add hprod (hFχ.const_mul c), intervalIntegral.integral_const_mul] at hFTC
  have hcoeff := fourierCoeff_eq_intervalIntegral (fun x => (f x : ℂ)) k (0 : ℝ)
  simp only [zero_add, smul_eq_mul, Complex.real_smul] at hcoeff
  have hcoeff' : (∫ t in (0 : ℝ)..T, F t * χ t) =
      (T : ℂ) * fourierCoeff (fun x => (f x : ℂ)) k := by
    rw [hcoeff]
    simp only [one_div, Complex.ofReal_inv]
    have heq : (∫ t in (0 : ℝ)..T, F t * χ t) =
        ∫ t in (0 : ℝ)..T, fourier (-k) (t : AddCircle T) * (f (t : AddCircle T) : ℂ) := by
      congr 1
      funext t
      exact mul_comm _ _
    rw [heq]
    field_simp [hT.out.ne']
  change (∫ t in (0 : ℝ)..T, q t * χ t) = _
  rw [hcoeff'] at hFTC
  dsimp [c] at hFTC
  linear_combination hFTC

end Riesz1.CircleFourier
