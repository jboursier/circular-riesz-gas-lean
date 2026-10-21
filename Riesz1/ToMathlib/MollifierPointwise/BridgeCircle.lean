/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.MollifierPointwise.Circle
public import Riesz1.ToMathlib.Mollifier.Periodization

/-!
# Bridge: the pointwise and Sobolev circle regularizations agree at length one

There are two regularizations on the circle. The pointwise object `circleMollify`
(`MollifierPointwise/Circle.lean`) convolves a real periodic function of length `L` with the periodized
mollifier. The Sobolev object `circleRegularize` (`Mollifier/Periodization.lean`) convolves a complex
function on `UnitAddCircle` with the periodized mollifier, and its input lies in the subtype of `L²`
functions. This file proves that the two agree at length one, for every `0 < h`.

Main results:
* `Riesz1.circleMollify_one_eq_integral`: for every function `g` on `UnitAddCircle` that lifts a real
  function `f`, the pointwise regularization of `f` is the real part of the integral that defines
  `circleRegularize`. No integrability is assumed. The range is `0 < h ≤ 1`.

The statement with `circleRegularize` itself is not stated here: `circleRegularize` is not exposed
(`@[expose]`), so its value cannot be unfolded from this module.
-/

public section

open MeasureTheory Set intervalIntegral

namespace Riesz1

variable {ρ : ℝ → ℝ}

/-- At a real point, the circle periodization is the real periodization `periodMollifier ρ 1 h`,
viewed in `ℂ`, for `0 < h ≤ 1`. -/
lemma circleMollifier_coe_real (hρ : IsMollifier ρ) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (u : ℝ) :
    circleMollifier ρ ⟨h, hh⟩ hρ.contDiff.continuous (u : UnitAddCircle) =
      ((periodMollifier ρ 1 h u : ℝ) : ℂ) := by
  have hc : IsCircleMollifier ρ :=
    ⟨hρ.contDiff, fun x => hρ.2.2.1 x, hρ.2.1, (subset_tsupport ρ).trans hρ.2.2.2.1, hρ.2.2.2.2⟩
  rw [circleMollifier_coe hc ⟨h, hh⟩ hh1 u, periodMollifier, Complex.ofReal_tsum]
  congr 1
  funext n
  simp [scaledMollifier, mul_one]

/-- The integral over `UnitAddCircle` is the integral over one period `[-1/2, 1/2]` of the lift. -/
lemma integral_unitAddCircle_eq_interval (F : UnitAddCircle → ℂ) :
    ∫ b : UnitAddCircle, F b = ∫ a in -(1 / 2 : ℝ)..(1 / 2 : ℝ), F (a : UnitAddCircle) := by
  rw [← AddCircle.intervalIntegral_preimage 1 (-(1 / 2 : ℝ)) F]
  norm_num

/-- **Bridge at length one, integral form.** Let `ρ` be a mollifier and `0 < h`. Let `g` be a
function on `UnitAddCircle` whose lift to `ℝ` is the real function `f`. Then, for every real `x`, the
pointwise regularization `circleMollify ρ 1 h f x` is the real part of the integral that defines
`circleRegularize` at `x`. No integrability of `f` is needed. The range is `0 < h ≤ 1`. -/
theorem circleMollify_one_eq_integral (hρ : IsMollifier ρ) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    {f : ℝ → ℝ} (g : UnitAddCircle → ℂ) (hg : ∀ t : ℝ, g (t : UnitAddCircle) = (f t : ℂ))
    (x : ℝ) :
    circleMollify ρ 1 h f x =
      (∫ y : UnitAddCircle, g y *
        circleMollifier ρ ⟨h, hh⟩ hρ.contDiff.continuous ((x : UnitAddCircle) - y)).re := by
  rw [integral_unitAddCircle_eq_interval]
  have hpt : ∀ a : ℝ, g (a : UnitAddCircle) *
      circleMollifier ρ ⟨h, hh⟩ hρ.contDiff.continuous ((x : UnitAddCircle) - (a : UnitAddCircle)) =
        ((f a * periodMollifier ρ 1 h (x - a) : ℝ) : ℂ) := by
    intro a
    rw [hg a, ← AddCircle.coe_sub, circleMollifier_coe_real hρ hh hh1, ← Complex.ofReal_mul]
  simp_rw [hpt]
  rw [intervalIntegral.integral_ofReal, Complex.ofReal_re]
  rfl

end Riesz1

end
