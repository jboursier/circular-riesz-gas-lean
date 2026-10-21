/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# An `L^p` norm bound from a moment bound

For a nonnegative measurable `g` and a real exponent `p > 0`, the `L^p` seminorm of `g` is at
most `M` as soon as `∫ g^p ≤ M^p`. This converts the inverse block moments of the Gibbs law into
`L^p` bounds in the exterior tail of Lemma 5.2.
-/

@[expose] public section

open MeasureTheory

namespace Riesz1

/-- **`L^p` bound from a moment.** Let `g ≥ 0` be measurable, `0 < p` and `0 ≤ M`. If
`∫ g^p dμ ≤ M^p`, then the `L^p` seminorm of `g` is at most `M`. -/
theorem eLpNorm_le_of_lintegral_rpow_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {g : Ω → ℝ} (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) {p M : ℝ} (hp : 0 < p) (hM : 0 ≤ M)
    (h : ∫⁻ x, ENNReal.ofReal (g x ^ p) ∂μ ≤ ENNReal.ofReal (M ^ p)) :
    eLpNorm g (ENNReal.ofReal p) μ ≤ ENNReal.ofReal M := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top
    hg.aestronglyMeasurable, ENNReal.toReal_ofReal hp.le]
  have hlin : ∫⁻ x, ‖g x‖ₑ ^ p ∂μ = ∫⁻ x, ENNReal.ofReal (g x ^ p) ∂μ :=
    lintegral_congr fun x => by
      rw [Real.enorm_eq_ofReal (hg0 x), ENNReal.ofReal_rpow_of_nonneg (hg0 x) hp.le]
  rw [hlin]
  have hMp : 0 ≤ M ^ p := Real.rpow_nonneg hM p
  calc (∫⁻ x, ENNReal.ofReal (g x ^ p) ∂μ) ^ (1 / p)
      ≤ (ENNReal.ofReal (M ^ p)) ^ (1 / p) := ENNReal.rpow_le_rpow h (by positivity)
    _ = ENNReal.ofReal ((M ^ p) ^ (1 / p)) := ENNReal.ofReal_rpow_of_nonneg hMp (by positivity)
    _ = ENNReal.ofReal M := by
        rw [one_div, Real.rpow_rpow_inv hM hp.ne']

end Riesz1

end
