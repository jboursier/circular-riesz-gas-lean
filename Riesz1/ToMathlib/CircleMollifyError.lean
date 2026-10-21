/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.MollifierPointwise.Circle

/-!
# Mollification error under a local Hölder increment bound

Let `ρ` be a mollifier, `h > 0` a scale and `f` a locally integrable function. If the increments
of `f` at a point `x` satisfy `|f(x - u) - f(x)| ≤ K |u|^θ` for `|u| ≤ h / 2`, then the
regularization `f_h` differs from `f` at `x` by at most `K (h / 2)^θ`. The line version is
`Riesz1.mollifyLine_sub_le_of_holder`. The circle version
`Riesz1.circleMollify_sub_le_of_holder` is its unfolding for a periodic `f`. A global Hölder
bound with the circle distance gives the circle version as a corollary
(`Riesz1.circleMollify_sub_le_of_circHolder`).

This is the error estimate behind the bound `|e_h| ≤ C h^{-α}` of
Lemma 5.3, where the increments of the profile have exponent `-α`.
-/

public section

open MeasureTheory Set Filter

namespace Riesz1

/-- **Line mollification error.** For a mollifier `ρ`, a scale `h > 0`, a locally integrable
`f`, and a point `x` at which `|f(x - u) - f(x)| ≤ K |u|^θ` for every `|u| ≤ h / 2`, the line
regularization satisfies `|f_h(x) - f(x)| ≤ K (h / 2)^θ`. -/
theorem mollifyLine_sub_le_of_holder {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {h : ℝ} (hh : 0 < h)
    {f : ℝ → ℝ} (hf : LocallyIntegrable f volume) {K θ : ℝ} (hK : 0 ≤ K) (hθ : 0 ≤ θ)
    (x : ℝ) (hH : ∀ u : ℝ, |u| ≤ h / 2 → |f (x - u) - f x| ≤ K * |u| ^ θ) :
    |mollifyLine ρ h f x - f x| ≤ K * (h / 2) ^ θ := by
  have hκ : Integrable (scaledMollifier ρ h) :=
    (contDiff_scaledMollifier hρ (h := h)).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_scaledMollifier hρ hh)
  have hint1 : Integrable fun u => f (x - u) * scaledMollifier ρ h u := by
    simpa only [sub_sub_cancel] using (integrable_mul_scaled_sub hρ hh hf x).comp_sub_left x
  have hint2 : Integrable fun u => f x * scaledMollifier ρ h u := hκ.const_mul (f x)
  -- The unit mass of the mollifier turns the constant `f x` into the subtracted term.
  have hsplit : ∫ u, (f (x - u) - f x) * scaledMollifier ρ h u = mollifyLine ρ h f x - f x := by
    simp_rw [sub_mul]
    rw [integral_sub hint1 hint2, ← mollifyLine_eq f x, integral_const_mul,
      integral_scaledMollifier hρ hh, mul_one]
  -- The error integrand is dominated by `K (h / 2)^θ` times the mollifier, since the mollifier
  -- vanishes for `|u| ≥ h / 2`.
  have hbound : ∀ u : ℝ, ‖(f (x - u) - f x) * scaledMollifier ρ h u‖ ≤
      (K * (h / 2) ^ θ) * scaledMollifier ρ h u := by
    intro u
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (scaledMollifier_nonneg hρ hh u)]
    by_cases hu : h / 2 ≤ |u|
    · rw [scaledMollifier_eq_zero hρ hh hu, mul_zero, mul_zero]
    · have h1 := hH u (not_le.mp hu).le
      have h2 : K * |u| ^ θ ≤ K * (h / 2) ^ θ :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg u) (not_le.mp hu).le hθ) hK
      exact mul_le_mul_of_nonneg_right (h1.trans h2) (scaledMollifier_nonneg hρ hh u)
  have hnorm := norm_integral_le_of_norm_le ((hκ.const_mul (K * (h / 2) ^ θ))) (Eventually.of_forall hbound)
  rw [integral_const_mul, integral_scaledMollifier hρ hh, mul_one, hsplit, Real.norm_eq_abs] at hnorm
  exact hnorm

/-- **Circle mollification error.** For a mollifier `ρ`, a length `L > 0`, a scale `h > 0`, and a
locally integrable `L`-periodic `f`, the circle regularization `f_h` of `f` satisfies
`|f_h(x) - f(x)| ≤ K (h / 2)^θ` at every `x` for which `|f(x - u) - f(x)| ≤ K |u|^θ` holds for
every `|u| ≤ h / 2`. -/
theorem circleMollify_sub_le_of_holder {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {L h : ℝ} (hL : 0 < L)
    (hh : 0 < h) {f : ℝ → ℝ} (hf : LocallyIntegrable f volume) (hper : Function.Periodic f L)
    {K θ : ℝ} (hK : 0 ≤ K) (hθ : 0 ≤ θ) (x : ℝ)
    (hH : ∀ u : ℝ, |u| ≤ h / 2 → |f (x - u) - f x| ≤ K * |u| ^ θ) :
    |circleMollify ρ L h f x - f x| ≤ K * (h / 2) ^ θ := by
  rw [circleMollify_eq_mollifyLine hρ hL hh hf hper x]
  exact mollifyLine_sub_le_of_holder hρ hh hf hK hθ x hH

/-- **Circle mollification error from a circle Hölder bound.** If `|f(y) - f(z)| ≤ K d(y - z)^θ`
for all `y, z`, where `d` is the circle distance `Riesz1.circDist`, then the circle regularization
satisfies `|f_h(x) - f(x)| ≤ K (h / 2)^θ` at every `x`. -/
theorem circleMollify_sub_le_of_circHolder {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {L h : ℝ}
    (hL : 0 < L) (hh : 0 < h) {f : ℝ → ℝ} (hf : LocallyIntegrable f volume)
    (hper : Function.Periodic f L) {K θ : ℝ} (hK : 0 ≤ K) (hθ : 0 ≤ θ)
    (hH : ∀ y z : ℝ, |f y - f z| ≤ K * circDist L (y - z) ^ θ) (x : ℝ) :
    |circleMollify ρ L h f x - f x| ≤ K * (h / 2) ^ θ := by
  refine circleMollify_sub_le_of_holder hρ hL hh hf hper hK hθ x fun u _ => ?_
  have hd : circDist L (x - u - x) ≤ |u| := by
    have := circDist_le_abs_sub hL (x - u - x) 0
    simpa [sub_sub_cancel_left, neg_sub, abs_neg] using this
  have hpow : circDist L (x - u - x) ^ θ ≤ |u| ^ θ :=
    Real.rpow_le_rpow (circDist_nonneg L _) hd hθ
  exact (hH (x - u) x).trans (mul_le_mul_of_nonneg_left hpow hK)

end Riesz1
