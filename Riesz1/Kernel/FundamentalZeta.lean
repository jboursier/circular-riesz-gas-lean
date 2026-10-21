/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.HurwitzKernel.Recurrence

/-!
# The Hurwitz zeta function: Euler summation, recurrence and differentiation

This is part of Lemma 2.1. The theorem `Riesz1.fundamental_zeta` collects its claims for
the Hurwitz zeta function `ζ(z, x)` at real `x > 0`, which is `Riesz1.hurwitzZetaPos`:

* for `Re z > 0` and `z ≠ 1`, the regularized partial sums converge to `ζ(z, x)` (the limit in
  equation (2.11)), and `ζ(z, x)` equals the integral formula with the sawtooth `B_1`.
* for real `z > -1` with `z ≠ 0, 1`, the function `x ↦ ζ(z, x)` is smooth on `(0, ∞)`, satisfies the
  recurrence `ζ(z, x) = x^{-z} + ζ(z, x + 1)`, and has derivative `∂_x ζ(z, x) = -z ζ(z + 1, x)`.

The hypotheses hold at `z = -s`, `1 - s`, `2 - s` for `0 < s < 1`, which is where the paper
uses the identities.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Riesz1

/-- The Hurwitz zeta function `ζ(z, x)` at real `x > 0` (part of Lemma 2.1).
For `Re z > 0` and `z ≠ 1`, the regularized partial sums converge to `ζ(z, x)`, and `ζ(z, x)`
equals the integral formula with the sawtooth `B_1(t) = t - ⌊t⌋ - 1/2`. For real `z > -1` with
`z ≠ 0, 1`, the function `x ↦ ζ(z, x)` is smooth on `(0, ∞)`, satisfies the recurrence, and has
derivative `-z ζ(z + 1, x)`. -/
theorem fundamental_zeta :
    (∀ x : ℝ, 0 < x → ∀ z : ℂ, 0 < z.re → z ≠ 1 →
      Tendsto (fun M : ℕ => (∑ n ∈ Finset.range (M + 1), ((n : ℂ) + x) ^ (-z)) -
          (M : ℂ) ^ (1 - z) / (1 - z)) atTop (𝓝 (hurwitzZetaPos z x)) ∧
        hurwitzZetaPos z x = (x : ℂ) ^ (1 - z) / (z - 1) + (x : ℂ) ^ (-z) / 2 -
          z * ∫ t in Ioi (0 : ℝ), ((sawtoothB1 t : ℝ) : ℂ) / ((t : ℂ) + x) ^ (1 + z)) ∧
    (∀ z : ℝ, -1 < z → z ≠ 0 → z ≠ 1 →
      ContDiffOn ℝ ∞ (fun x : ℝ => hurwitzZetaPos (z : ℂ) x) (Ioi 0) ∧
        (∀ x : ℝ, 0 < x →
          hurwitzZetaPos (z : ℂ) x = (x : ℂ) ^ (-(z : ℂ)) + hurwitzZetaPos (z : ℂ) (x + 1)) ∧
        (∀ x : ℝ, 0 < x →
          HasDerivAt (fun y : ℝ => hurwitzZetaPos (z : ℂ) y)
            (-(z : ℂ) * hurwitzZetaPos ((z : ℂ) + 1) x) x)) := by
  refine ⟨fun x hx z hz0 hz1 => ⟨tendsto_hurwitzZetaPos hx hz0 hz1,
    hurwitzZetaPos_eq_integral hx hz0 hz1⟩, fun z hz hz0 hz1 => ?_⟩
  have hre : -1 < ((z : ℂ)).re := by rw [Complex.ofReal_re]; exact hz
  have hc1 : (z : ℂ) ≠ 1 := by exact_mod_cast hz1
  have hc0 : (z : ℂ) ≠ 0 := by exact_mod_cast hz0
  refine ⟨contDiffOn_hurwitzZetaPos hre hc1, fun x hx => hurwitzZetaPos_recurrence hx _, fun x hx =>
    hasDerivAt_hurwitzZetaPos hre hc0 hc1 hx⟩

end Riesz1

end
