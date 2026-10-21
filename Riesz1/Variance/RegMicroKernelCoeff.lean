/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroKernelFubini
public import Riesz1.Kernel.FundamentalSolution
public import Riesz1.Kernel.TransportScaledConvolution

/-!
# Fourier coefficients of the inverse-transport kernel

This file computes the Fourier coefficient of `P_L(t) = -2β L^{-s} g_s(t/L)` on the cell
`(-L/2, L/2]` against the character `charE L k`. Rescaling `t = L u` turns the coefficient into the
coefficient of the Riesz kernel `g_s` on the unit circle, which `Riesz1.fundamental` gives
explicitly as `c_s (2π|k|)^{s-1}`. This is the multiplier identity in the proof of
Lemma 5.3: `L P̂_L(k) = -2β c_s |2πk/L|^{-τ}`.
-/

public section

open MeasureTheory Set intervalIntegral Filter Topology Complex
open scoped ContDiff Real

namespace Riesz1

/-- The character `charE L k` evaluated at `L u` is the unit-length character `charE 1 k` at `u`. -/
lemma charE_mul_left_eq_unit {L : ℝ} (hL : L ≠ 0) (k : ℤ) (u : ℝ) :
    charE L k (L * u) = charE 1 k u := by
  unfold charE
  congr 2
  field_simp

/-- **Fourier coefficient of `P_L` on the cell.** For `L > 0` and every integer `k`, the
integral of `P_L(x) e_k(x)` over `(-L/2, L/2]` equals `L · (-2β L^{-s}) · ĝ_s(k)`, where `ĝ_s` is
the normalized Fourier coefficient of the Riesz kernel on the unit circle. -/
lemma integral_inverseKernel_charE_cell (P : Parameters) {L : ℝ} (hL : 0 < L) (k : ℤ) :
    ∫ x in Ioc (-(L / 2)) (L / 2), (inverseKernel P L x : ℂ) * charE L k x =
      (L : ℂ) * ((-(2 * P.val.1 * L ^ (-P.val.2)) : ℝ) : ℂ) *
        fourierCoeff (fun u : UnitAddCircle =>
          (rieszRepresentative (parametersExponent P) u : ℂ)) k := by
  have hle : -(L / 2) ≤ L / 2 := by linarith
  rw [← intervalIntegral.integral_of_le hle]
  set F : ℝ → ℂ := fun x => (inverseKernel P L x : ℂ) * charE L k x with hF
  have hscale := intervalIntegral.integral_comp_mul_left (a := -(1 / 2)) (b := 1 / 2) F hL.ne'
  rw [show L * (-(1 / 2)) = -(L / 2) by ring, show L * (1 / 2) = L / 2 by ring] at hscale
  -- the rescaled integrand is the unit-circle integrand times the constant `-2β L^{-s}`
  have hpt : ∀ u : ℝ, F (L * u) = ((-(2 * P.val.1 * L ^ (-P.val.2)) : ℝ) : ℂ) *
      (charE 1 k u * ((rieszRepresentative (parametersExponent P) (u : UnitAddCircle) : ℝ) : ℂ)) := by
    intro u
    simp only [hF]
    rw [charE_mul_left_eq_unit hL.ne' k u, inverseKernel]
    have hdiv : L * u / L = u := by field_simp
    rw [hdiv]
    push_cast
    ring
  have hI : ∫ x in (-(L / 2))..(L / 2), F x = (L : ℂ) *
      ((-(2 * P.val.1 * L ^ (-P.val.2)) : ℝ) : ℂ) *
        fourierCoeff (fun u : UnitAddCircle =>
          (rieszRepresentative (parametersExponent P) u : ℂ)) k := by
    have h1 : ∫ x in (-(L / 2))..(L / 2), F x = L • ∫ u in (-(1 / 2))..(1 / 2), F (L * u) := by
      rw [hscale, smul_inv_smul₀ hL.ne']
    rw [h1, intervalIntegral.integral_congr (fun u _ => hpt u), Complex.real_smul,
      fourierCoeff_eq_intervalIntegral _ k (-(1 / 2)), show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num,
      div_one, one_smul]
    simp only [mul_assoc, smul_eq_mul, fourier_neg_coe_eq_charE]
    rw [intervalIntegral.integral_const_mul]
  rw [hI]

end Riesz1

end
