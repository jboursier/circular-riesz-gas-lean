/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.CircleMollifyBounds
public import Riesz1.Bridges.Mollifier
public import Riesz1.ToMathlib.Mollifier.Periodization

/-!
# Fourier coefficients of the regularization at every circle length

The multiplier is `m(h k / L)`, where `m` is `mollifierFT`.
There is no change from arclength convolution to normalized convolution.
-/

public section

open MeasureTheory Set Filter Real
open scoped FourierTransform

namespace Riesz1.Internal

theorem fourierCoeff_circleMollify {ρ : ℝ → ℝ} (hρ : IsMollifier ρ)
    {L h : ℝ} [hL : Fact (0 < L)] (hh : 0 < h)
    {F : ℝ → ℝ} (hF : LocallyIntegrable F volume) (hp : Function.Periodic F L)
    (f g : AddCircle L → ℝ) (hf : ∀ x : ℝ, f (x : AddCircle L) = F x)
    (hg : ∀ x : ℝ, g (x : AddCircle L) = circleMollify ρ L h F x) (k : ℤ) :
    fourierCoeff (fun x => (g x : ℂ)) k =
      fourierCoeff (fun x => (f x : ℂ)) k * (mollifierFT ρ (h * k / L) : ℂ) := by
  let χ : ℝ → ℂ := fun x => fourier (-k) (x : AddCircle L)
  have hχc : Continuous χ := (fourier (-k)).continuous.comp (AddCircle.continuous_mk' L)
  have hχn (x : ℝ) : ‖χ x‖ = 1 := by
    change ‖(AddCircle.toCircle (-k • (x : AddCircle L)) : ℂ)‖ = 1
    exact Circle.norm_coe _
  have hχadd (x y : ℝ) : χ (x + y) = χ x * χ y := by
    simp only [χ, AddCircle.coe_add, fourier_apply, smul_add,
      AddCircle.toCircle_add, Circle.coe_mul]
  have hχp : Function.Periodic χ L := by intro x; simp only [χ, AddCircle.coe_add_period]
  let κ := scaledMollifier ρ h
  have hκc : Continuous κ := (contDiff_scaledMollifier hρ).continuous
  have hκs : HasCompactSupport κ := hasCompactSupport_scaledMollifier hρ hh
  have hi : Integrable (fun p : ℝ × ℝ =>
      (F (p.1 - p.2) * κ p.2 : ℝ) * χ p.1)
      ((volume.restrict (Ioc (-(L / 2)) (L / 2))).prod volume) :=
    (integrable_prod_sub_mul hF hκc hκs).ofReal.mul_bdd
      (hχc.comp continuous_fst).aestronglyMeasurable
      (ae_of_all _ fun p => (hχn p.1).le)
  have hcv (x : ℝ) : circleMollify ρ L h F x = ∫ u, F (x - u) * κ u := by
    rw [circleMollify_eq_mollifyLine hρ hL.out hh hF hp, mollifyLine_eq]
  have hfp : Function.Periodic (fun x => (F x : ℂ) * χ x) L := by
    intro x
    dsimp only
    rw [hp x, hχp x]
  have hshift (u : ℝ) :
      ∫ x in Ioc (-(L / 2)) (L / 2), (F (x - u) * κ u : ℝ) * χ x =
        (∫ x in Ioc (-(L / 2)) (L / 2), (F x : ℂ) * χ x) *
          ((κ u : ℂ) * χ u) := by
    have he (x : ℝ) : (F (x - u) * κ u : ℝ) * χ x =
        ((F (x - u) : ℂ) * χ (x - u)) * ((κ u : ℂ) * χ u) := by
      have hx : χ x = χ (x - u) * χ u := by rw [← hχadd, sub_add_cancel]
      rw [hx]
      push_cast
      ring
    simp_rw [he]
    rw [integral_mul_const]
    congr 1
    rw [← intervalIntegral.integral_of_le (by linarith [hL.out] : -(L / 2) ≤ L / 2),
      ← intervalIntegral.integral_of_le (by linarith [hL.out] : -(L / 2) ≤ L / 2)]
    change (∫ x in (-(L / 2))..(L / 2),
      (fun t => (F t : ℂ) * χ t) (x - u)) = _
    rw [intervalIntegral.integral_comp_sub_right (fun t => (F t : ℂ) * χ t) u]
    have ht := hfp.intervalIntegral_add_eq (-(L / 2) - u) (-(L / 2))
    simpa only [show -(L / 2) - u + L = L / 2 - u by ring,
      show -(L / 2) + L = L / 2 by ring] using ht
  have hκFT : (∫ u, (κ u : ℂ) * χ u) = (mollifierFT ρ (h * k / L) : ℂ) := by
    have he (u : ℝ) : (κ u : ℂ) * χ u =
        Complex.exp (↑(-2 * Real.pi * u * ((k : ℝ) / L)) * Complex.I) *
          ((h⁻¹ * ρ (u / h) : ℝ) : ℂ) := by
      change ((h⁻¹ * ρ (u / h) : ℝ) : ℂ) * fourier (-k) (u : AddCircle L) = _
      rw [fourier_coe_apply]
      have ha : 2 * (Real.pi : ℂ) * Complex.I * (-k : ℤ) * u / L =
          ↑(-2 * Real.pi * u * ((k : ℝ) / L)) * Complex.I := by
        push_cast
        ring
      rw [ha, mul_comm]
    simp_rw [he]
    change (∫ u, Complex.exp (↑(-2 * π * u * ((k : ℝ) / L)) * Complex.I) •
      ((h⁻¹ * ρ (u / h) : ℝ) : ℂ)) = _
    rw [← fourier_real_eq_integral_exp_smul]
    rw [fourier_kernel_eq ρ hh, mollifierFT_ofReal hρ.isCircleMollifier]
    congr 2
    ring
  have hmain : (∫ x in Ioc (-(L / 2)) (L / 2),
      (circleMollify ρ L h F x : ℂ) * χ x) =
      (∫ x in Ioc (-(L / 2)) (L / 2), (F x : ℂ) * χ x) *
        (mollifierFT ρ (h * k / L) : ℂ) := by
    simp_rw [hcv]
    simp_rw [← integral_complex_ofReal]
    simp_rw [← integral_mul_const]
    rw [integral_integral_swap hi]
    simp_rw [hshift]
    rw [integral_const_mul, hκFT, integral_mul_const]
  rw [fourierCoeff_eq_intervalIntegral _ k (-(L / 2)),
    fourierCoeff_eq_intervalIntegral _ k (-(L / 2))]
  simp only [show -(L / 2) + L = L / 2 by ring, smul_eq_mul, hf, hg]
  rw [intervalIntegral.integral_of_le (by linarith [hL.out] : -(L / 2) ≤ L / 2),
    intervalIntegral.integral_of_le (by linarith [hL.out] : -(L / 2) ≤ L / 2)]
  have hmain' := hmain
  simp_rw [mul_comm (_ : ℂ) (χ _)] at hmain'
  change (1 / L : ℝ) • _ = ((1 / L : ℝ) • _) * _
  rw [hmain']
  simp only [Complex.real_smul]
  ring

end Riesz1.Internal
