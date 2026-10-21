/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.InterchangeHeat
public import Riesz1.Kernel.InterchangeSum
public import Riesz1.Frozen.RieszConstant
public import Riesz1.Frozen.RieszRepresentative
public import Mathlib.Tactic

/-!
# Absolute interchange for the fundamental solution

This is part of the proof of Lemma 2.1.
For `0 < s < 1` and `0 < x < 1`, with `u_k^x(t) = t^{-1-s/2} (e^{-(x-k)^2/(4t)} - ∫_0^1 e^{-(y-k)^2/(4t)} dy)`:

* `∑_k ∫_{(0,∞)} |u_k^x(t)| dt < ∞`, and each integral is finite.
* `(c_s / Γ((1-s)/2)) ∫_{(0,∞)} (W_t(x) - 1) t^{-(1+s)/2} dt
    = (c_s / (Γ((1-s)/2) √(4π))) ∑_k ∫_{(0,∞)} u_k^x(t) dt = g_s(x)`,

where `W_t` is the heat kernel on the circle, `c_s` is the Riesz normalization,
and `g_s` is the periodic Riesz kernel, here `rieszRepresentative`.

The proof writes `u_k^x` as the difference of two integrable terms, evaluates the time integrals with
the reciprocal-time Gamma integral, uses the periodized Gaussian formula for the heat kernel and the
summability of the absolute integrals to exchange sum and integral, and identifies the centered
series with the renormalized symmetric sum of `rieszRepresentative`.

Main result:
* `Riesz1.fundamental_interchange`.
-/

public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace Riesz1

/-- The constant `c_s/(Γ((1-s)/2)√(4π)) · Γ(s/2) 2^s` equals one, by the duplication of the square
root `√(4π) = 2√π` and `2^{1-s} 2^s = 2`. -/
lemma riesz_constant_mul_eq_one (s : RieszExponent) :
    rieszConstant s / (Real.Gamma ((1 - s.val) / 2) * Real.sqrt (4 * π)) *
      (Real.Gamma (s.val / 2) * 2 ^ s.val) = 1 := by
  have hs0 : 0 < s.val := s.2.1
  have hs1 : s.val < 1 := s.2.2
  have hΓ1 : Real.Gamma ((1 - s.val) / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hΓ2 : Real.Gamma (s.val / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hsq : Real.sqrt (4 * π) = 2 * Real.sqrt π := by
    rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  have hpow : (2 : ℝ) ^ (1 - s.val) * 2 ^ s.val = 2 := by
    rw [← Real.rpow_add (by norm_num)]
    norm_num
  have hsqrtπ : Real.sqrt π ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  unfold rieszConstant
  rw [hsq]
  field_simp
  linear_combination hpow

/-- The Gamma-integral value of each interchange integral, in the Riesz form:
`∫_{(0,∞)} u_k^x(t) dt = Γ(s/2) 2^s (|x-k|^{-s} - ∫_0^1 |y-k|^{-s} dy)`. -/
lemma integral_interchangeTerm_riesz {s x : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hx0 : 0 < x)
    (hx1 : x < 1) (k : ℤ) :
    ∫ t in Ioi (0 : ℝ), interchangeTerm s x k t =
      (Real.Gamma (s / 2) * 2 ^ s) *
        (|x - (k : ℝ)| ^ (-s) - ∫ y in (0 : ℝ)..1, |y - (k : ℝ)| ^ (-s)) := by
  rw [integral_interchangeTerm hs0 hs1 hx0 hx1 k]
  have hint : ∫ y in (0 : ℝ)..1, ((y - k) ^ 2 / 4) ^ (-(s / 2)) =
      2 ^ s * ∫ y in (0 : ℝ)..1, |y - (k : ℝ)| ^ (-s) := by
    simp_rw [rpow_sq_div_four_neg_half]
    rw [intervalIntegral.integral_const_mul]
  rw [hint, rpow_sq_div_four_neg_half]
  ring

/-- **Absolute interchange for the fundamental solution** (part of the proof of Lemma 2.1).
Let `0 < s < 1` and `0 < x < 1`. Then each interchange integrand `u_k^x` is integrable on `(0, ∞)`,
the sum of the absolute integrals converges, and the time integral of `(W_t(x) - 1) t^{-(1+s)/2}`
equals `(c_s/(Γ((1-s)/2)√(4π)))` times the sum of the integrals of `u_k^x`, which equals the
periodic Riesz kernel `g_s(x) = rieszRepresentative s x`. The heat kernel `W_t(x)` is written as
the series `∑_k e^{-4π²k²t} cos(2πkx)`, which is `circleHeatKernel t _ x` for `t > 0`. -/
theorem fundamental_interchange (s : RieszExponent) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    (∀ k : ℤ, IntegrableOn (interchangeTerm s.val x k) (Ioi 0)) ∧
    Summable (fun k : ℤ => ∫ t in Ioi (0 : ℝ), |interchangeTerm s.val x k t|) ∧
    (rieszConstant s / Real.Gamma ((1 - s.val) / 2) *
        ∫ t in Ioi (0 : ℝ), (∑' k : ℤ, Real.exp (-4 * π ^ 2 * (k : ℝ) ^ 2 * t) *
          Real.cos (2 * π * k * x) - 1) * t ^ (-(1 + s.val) / 2) =
      rieszConstant s / (Real.Gamma ((1 - s.val) / 2) * Real.sqrt (4 * π)) *
        ∑' k : ℤ, ∫ t in Ioi (0 : ℝ), interchangeTerm s.val x k t) ∧
    rieszConstant s / (Real.Gamma ((1 - s.val) / 2) * Real.sqrt (4 * π)) *
        ∑' k : ℤ, ∫ t in Ioi (0 : ℝ), interchangeTerm s.val x k t =
      rieszRepresentative s (x : UnitAddCircle) := by
  have hs0 : 0 < s.val := s.2.1
  have hs1 : s.val < 1 := s.2.2
  have hcoef : Real.Gamma (s.val / 2) * 2 ^ s.val ≠ 0 :=
    mul_ne_zero (Real.Gamma_pos_of_pos (by linarith)).ne' (Real.rpow_pos_of_pos two_pos _).ne'
  have hsum := summable_integral_abs_interchangeTerm hs0 hs1 hx0 hx1
  -- The integrals of `u_k^x` are summable, since they are dominated by the absolute integrals.
  have hsumU : Summable (fun k : ℤ => ∫ t in Ioi (0 : ℝ), interchangeTerm s.val x k t) :=
    Summable.of_norm_bounded hsum (fun k => by
      refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
      simp only [Real.norm_eq_abs])
  -- The centered series is summable, being a multiple of the summable integrals.
  have hb : Summable fun k : ℤ =>
      |x - (k : ℝ)| ^ (-s.val) - ∫ y in (0 : ℝ)..1, |y - (k : ℝ)| ^ (-s.val) := by
    refine (hsumU.mul_left (Real.Gamma (s.val / 2) * 2 ^ s.val)⁻¹).congr (fun k => ?_)
    rw [integral_interchangeTerm_riesz hs0 hs1 hx0 hx1 k, ← mul_assoc, inv_mul_cancel₀ hcoef,
      one_mul]
  have hval : ∑' k : ℤ, ∫ t in Ioi (0 : ℝ), interchangeTerm s.val x k t =
      (Real.Gamma (s.val / 2) * 2 ^ s.val) *
        (2 * (HurwitzZeta.hurwitzZetaEven (x : UnitAddCircle) (s.val : ℂ)).re) := by
    simp_rw [integral_interchangeTerm_riesz hs0 hs1 hx0 hx1]
    rw [tsum_mul_left, tsum_centered_eq_riesz hs0 hs1 hx0 hx1 hb]
  have hK : (4 * π) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (4 * π))⁻¹ := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg (by positivity)]
  refine ⟨fun k => integrableOn_interchangeTerm hs0 hs1 hx0 hx1 k, hsum, ?_, ?_⟩
  · rw [integral_heat_eq_interchange hs0 hs1 hx0 hx1, hK]
    ring
  · rw [hval, ← mul_assoc, riesz_constant_mul_eq_one s, one_mul]
    rfl

end Riesz1
