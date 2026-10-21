/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.MollifierPointwise.BridgeCircle
public import Riesz1.ToMathlib.Mollifier.Periodization

/-!
# Bridge: the pointwise regularization is the `L²` regularization at length one

Mollification at length `L = 1`. The pointwise object `circleMollify ρ 1 h f`
(`MollifierPointwise/Circle.lean`) is a real periodic function on `ℝ`. The Sobolev object
`circleRegularize ρ h _ ξ` (`Mollifier/Periodization.lean`) is a complex function on `UnitAddCircle`,
applied to an `L²` class `ξ`. This file proves that the two agree at every real point, for
`0 < h ≤ 1`.

Main results:
* `Riesz1.circleMollify_one_eq_complex_integral`: for every function `g` on `UnitAddCircle` that
  lifts a real function `f`, the value `(circleMollify ρ 1 h f x : ℂ)` equals the integral that
  defines `circleRegularize` at `x`. No integrability is assumed.
* `Riesz1.circleMollify_one_eq_circleRegularize`: the same identity with `circleRegularize` itself,
  for an `L²` class `g` lifting `f`. The `L²` hypothesis is forced by the type of the input of
  `circleRegularize`.

Periodicity of `f` is not a separate hypothesis: `g` is a function on `UnitAddCircle` whose lift
is `f`, so `f` has period one.
-/

public section

open MeasureTheory Set intervalIntegral

namespace Riesz1

variable {ρ : ℝ → ℝ}

/-- The periodized mollifier at every point of `UnitAddCircle` is real for `0 < h ≤ 1`. -/
lemma circleMollifier_im_eq_zero (hρ : IsMollifier ρ) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1)
    (z : UnitAddCircle) :
    (circleMollifier ρ ⟨h, hh⟩ hρ.contDiff.continuous z).im = 0 := by
  induction z using QuotientAddGroup.induction_on with
  | H u => rw [circleMollifier_coe_real hρ hh hh1 u, Complex.ofReal_im]

/-- A function `g` on `UnitAddCircle` that lifts a real function is real valued everywhere. -/
lemma im_eq_zero_of_lift {f : ℝ → ℝ} {g : UnitAddCircle → ℂ} (hg : ∀ t : ℝ, g t = f t)
    (y : UnitAddCircle) : (g y).im = 0 := by
  induction y using QuotientAddGroup.induction_on with
  | H t => rw [hg t, Complex.ofReal_im]

/-- **Bridge at length one, complex integral form.** Let `ρ` be a mollifier and `0 < h ≤ 1`. Let `g`
be a function on `UnitAddCircle` whose lift is the real function `f`. Then, for every real `x`,
the pointwise regularization `circleMollify ρ 1 h f x`, viewed in `ℂ`, equals the integral over
`UnitAddCircle` of `g y` times the periodized mollifier at `x - y`. No integrability of `g` is
assumed, because the integrand is real and the integral of a real function is its real integral in
either case. -/
theorem circleMollify_one_eq_complex_integral (hρ : IsMollifier ρ) {h : ℝ} (hh : 0 < h)
    (hh1 : h ≤ 1) {f : ℝ → ℝ} (g : UnitAddCircle → ℂ) (hg : ∀ t : ℝ, g t = f t) (x : ℝ) :
    (circleMollify ρ 1 h f x : ℂ) =
      ∫ y : UnitAddCircle, g y *
        circleMollifier ρ ⟨h, hh⟩ hρ.contDiff.continuous ((x : UnitAddCircle) - y) := by
  -- The integrand is real at each `y`, so the integral is the complex lift of a real integral.
  have hreal : ∀ y : UnitAddCircle, g y *
      circleMollifier ρ ⟨h, hh⟩ hρ.contDiff.continuous ((x : UnitAddCircle) - y) =
      ((g y * circleMollifier ρ ⟨h, hh⟩ hρ.contDiff.continuous ((x : UnitAddCircle) - y)).re : ℂ) := by
    intro y
    have him : (g y * circleMollifier ρ ⟨h, hh⟩ hρ.contDiff.continuous
        ((x : UnitAddCircle) - y)).im = 0 := by
      rw [Complex.mul_im, im_eq_zero_of_lift hg y,
        circleMollifier_im_eq_zero hρ hh hh1]
      ring
    exact Complex.ext (Complex.ofReal_re _).symm (by rw [him, Complex.ofReal_im])
  have hint : ∫ y : UnitAddCircle, g y *
      circleMollifier ρ ⟨h, hh⟩ hρ.contDiff.continuous ((x : UnitAddCircle) - y) =
      ((∫ y : UnitAddCircle, (g y *
        circleMollifier ρ ⟨h, hh⟩ hρ.contDiff.continuous ((x : UnitAddCircle) - y)).re : ℝ) : ℂ) := by
    exact (integral_congr_ae (Filter.Eventually.of_forall hreal)).trans _root_.integral_ofReal
  -- The real part of the complex integral is the real integral, by `hint`.
  have hreal_part : circleMollify ρ 1 h f x = ∫ y : UnitAddCircle, (g y *
      circleMollifier ρ ⟨h, hh⟩ hρ.contDiff.continuous ((x : UnitAddCircle) - y)).re := by
    rw [circleMollify_one_eq_integral hρ hh hh1 g hg x, hint, Complex.ofReal_re]
  rw [hreal_part, hint]

/-- **Bridge at length one, `L²` form.** Let `ρ` be a mollifier and `0 < h ≤ 1`. Let `g` be
an `L²` function on `UnitAddCircle` whose lift is the real function `f`. Then, for every real `x`,
the pointwise regularization `circleMollify ρ 1 h f x`, viewed in `ℂ`, equals the Sobolev
regularization `circleRegularize` applied to the class of `g`, evaluated at the class of `x`. Thus
`circleMollify ρ 1 h f` is a representative of `circleRegularize` applied to the class of `f`. -/
theorem circleMollify_one_eq_circleRegularize (hρ : IsMollifier ρ) {h : ℝ} (hh : 0 < h)
    (hh1 : h ≤ 1) {f : ℝ → ℝ} (g : UnitAddCircle → ℂ) (hg : ∀ t : ℝ, g t = f t)
    (hgL2 : MemLp g 2 volume) (x : ℝ) :
    (circleMollify ρ 1 h f x : ℂ) =
      circleRegularize ρ ⟨h, hh⟩ hρ.contDiff.continuous ⟨g, hgL2⟩ (x : UnitAddCircle) :=
  circleMollify_one_eq_complex_integral hρ hh hh1 g hg x

end Riesz1

end
