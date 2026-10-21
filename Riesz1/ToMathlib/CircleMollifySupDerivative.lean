/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.MollifierPointwise.Derivative

/-!
# A derivative bound from the supremum of a periodic input

The derivative falls on the smooth kernel. The coefficient is its actual
integrable derivative norm, and is independent of the input function.
-/

public section

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace Riesz1

/-- A bounded continuous periodic input has a uniformly bounded smoothed
derivative, with the derivative norm of the scaled mollifier as coefficient. -/
theorem circleMollify_deriv_le_sup {ρ f : ℝ → ℝ} (hρ : IsMollifier ρ)
    {L h B : ℝ} (hL : 0 < L) (hh : 0 < h) (hf : Continuous f)
    (hp : Function.Periodic f L) (hb : ∀ x, |f x| ≤ B) (x : ℝ) :
    |deriv (circleMollify ρ L h f) x| ≤
      B * ∫ u, |deriv (scaledMollifier ρ h) u| := by
  let κ := scaledMollifier ρ h
  have hc : ContDiff ℝ ∞ κ := contDiff_scaledMollifier hρ
  have hcs : HasCompactSupport κ := hasCompactSupport_scaledMollifier hρ hh
  have hdc : Continuous (deriv κ) := hc.continuous_deriv (by simp)
  have hdi : Integrable (deriv κ) := hdc.integrable_of_hasCompactSupport hcs.deriv
  rw [circleMollify_fun_eq hρ hL hh hf.locallyIntegrable hp,
    (hasDerivAt_integral_mul_sub_kernel hf.locallyIntegrable hcs
      (hc.of_le (by simp)) x).deriv]
  have hcv : (∫ y, f y * deriv κ (x - y)) = ∫ u, f (x - u) * deriv κ u := by
    rw [← integral_sub_left_eq_self (fun y => f y * deriv κ (x - y)) volume x]
    simp only [sub_sub_cancel]
  rw [hcv]
  have hi : Integrable (fun u => f (x - u) * deriv κ u) :=
    ((hf.comp (continuous_const.sub continuous_id)).mul hdc).integrable_of_hasCompactSupport
      hcs.deriv.mul_left
  calc
    _ ≤ ∫ u, |f (x - u) * deriv κ u| := by
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (fun u => f (x - u) * deriv κ u)
    _ ≤ ∫ u, B * |deriv κ u| := by
      apply integral_mono hi.abs (hdi.abs.const_mul B)
      intro u
      dsimp only
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hb _) (abs_nonneg _)
    _ = _ := integral_const_mul _ _

end Riesz1

end
