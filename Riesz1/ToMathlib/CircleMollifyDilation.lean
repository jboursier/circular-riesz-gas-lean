/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.CircleMollifyBounds

/-!
# Dilation of the actual circle regularization

Pullback from length `L` to length one changes the physical radius `h` to `h / L`.
The identities use arclength in both convolutions.
-/

public section

open MeasureTheory

namespace Riesz1.Internal

theorem periodMollifier_dilation (ρ : ℝ → ℝ) {L h : ℝ}
    (hL : L ≠ 0) (hh : h ≠ 0) (z : ℝ) :
    periodMollifier ρ 1 (h / L) z = L * periodMollifier ρ L h (L * z) := by
  unfold periodMollifier
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  simp only [scaledMollifier]
  have he : (z + (n : ℝ) * 1) / (h / L) = (L * z + (n : ℝ) * L) / h := by
    field_simp
  rw [he]
  field_simp

theorem circleMollify_dilation (ρ : ℝ → ℝ) {L h : ℝ}
    (hL : L ≠ 0) (hh : h ≠ 0) (f : ℝ → ℝ) (x : ℝ) :
    circleMollify ρ 1 (h / L) (fun t => f (L * t)) x =
      circleMollify ρ L h f (L * x) := by
  unfold circleMollify
  simp_rw [periodMollifier_dilation ρ hL hh]
  have he (y : ℝ) : f (L * y) * (L * periodMollifier ρ L h (L * (x - y))) =
      L * ((fun u => f u * periodMollifier ρ L h (L * x - u)) (L * y)) := by
    rw [mul_sub]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul]
  change L * (∫ y in (-(1 / 2 : ℝ))..(1 / 2),
    (fun u => f u * periodMollifier ρ L h (L * x - u)) (L * y)) = _
  rw [intervalIntegral.integral_comp_mul_left
      (fun u => f u * periodMollifier ρ L h (L * x - u)) hL,
    smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hL, one_mul]
  congr 1 <;> ring

end Riesz1.Internal
