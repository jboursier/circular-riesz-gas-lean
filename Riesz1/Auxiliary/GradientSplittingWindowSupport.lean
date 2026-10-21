/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingWindowKernel

/-!
# Support of the coefficient `ψ` near the window endpoints

In a partial window the background set is `B = [-t, t]`, and `ψ(y/ℓ) = 0` whenever every integer
`m` satisfies `t/4 ≤ |y - m|` (the support assumption). When an endpoint
`-t - x` or `t - x` of the `v`-frame integral is an integer, the lift `x` is at distance at least `t`
from every integer. Then `ψ`, `ψ'` vanish at `x/ℓ` and near it, and the coefficients of the principal
values vanish on a neighbourhood of the integer endpoint.
-/

@[expose] public section

open Set Filter Topology

namespace Riesz1

noncomputable section

/-- For `0 < t ≤ 1/2` and every integer `j`, the point `t + j` is at distance at least `t` from `0`. -/
lemma le_abs_add_int {t : ℝ} (ht : 0 < t) (ht2 : t ≤ 1 / 2) (j : ℤ) : t ≤ |t + j| := by
  rcases le_or_gt 0 j with h | h
  · have hj : (0 : ℝ) ≤ j := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have hj : (j : ℝ) ≤ -1 := by
      have : j ≤ -1 := by omega
      exact_mod_cast this
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- A lift at an integer endpoint `-t - n` or `t - n` is at distance at least `t` from every
integer. -/
lemma far_of_endpoint {t x : ℝ} (ht : 0 < t) (ht2 : t ≤ 1 / 2)
    (hx : (∃ n : ℤ, x = -t - n) ∨ (∃ n : ℤ, x = t - n)) : ∀ m : ℤ, t ≤ |x - m| := by
  intro m
  rcases hx with ⟨n, hn⟩ | ⟨n, hn⟩
  · have h : x - m = -(t + ((n + m : ℤ) : ℝ)) := by rw [hn]; push_cast; ring
    rw [h, abs_neg]
    exact le_abs_add_int ht ht2 (n + m)
  · have h : x - m = t + ((-(n + m) : ℤ) : ℝ) := by rw [hn]; push_cast; ring
    rw [h]
    exact le_abs_add_int ht ht2 (-(n + m))

/-- `ψ(y/ℓ)` vanishes near every point at distance at least `t` from the integers. -/
lemma eventually_psi_zero_near {ψ : ℝ → ℝ} {ℓ t : ℝ} (ht : 0 < t)
    (hsupp : ∀ y : ℝ, (∀ m : ℤ, t / 4 ≤ |y - m|) → ψ (y / ℓ) = 0) {c : ℝ}
    (hc : ∀ m : ℤ, t ≤ |c - m|) : ∀ᶠ y in 𝓝 c, ψ (y / ℓ) = 0 := by
  filter_upwards [Metric.ball_mem_nhds c (by linarith : (0 : ℝ) < 3 * t / 4)] with y hy
  apply hsupp
  intro m
  have h1 : |c - m| ≤ |c - y| + |y - m| := abs_sub_le c y m
  have h2 : |c - y| < 3 * t / 4 := by
    rw [Metric.mem_ball, Real.dist_eq] at hy
    rw [abs_sub_comm]; exact hy
  have h3 := hc m
  linarith

/-- The derivative `ψ'(x/ℓ)` vanishes when `ψ(y/ℓ)` vanishes near `x`. -/
lemma deriv_psi_zero_of_eventually {ψ : ℝ → ℝ} {ℓ : ℝ} (hℓ : ℓ ≠ 0) {x : ℝ}
    (hz : ∀ᶠ y in 𝓝 x, ψ (y / ℓ) = 0) (hψ : DifferentiableAt ℝ ψ (x / ℓ)) :
    deriv ψ (x / ℓ) = 0 := by
  have hchain : HasDerivAt (fun y : ℝ => ψ (y / ℓ)) (deriv ψ (x / ℓ) * (1 / ℓ)) x := by
    have hlin : HasDerivAt (fun y : ℝ => y / ℓ) (1 / ℓ) x := by
      simpa using (hasDerivAt_id x).div_const ℓ
    exact hψ.hasDerivAt.comp x hlin
  have hzero : HasDerivAt (fun y : ℝ => ψ (y / ℓ)) 0 x :=
    (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hz
  have h := hchain.unique hzero
  have hℓinv : (1 / ℓ) ≠ 0 := one_div_ne_zero hℓ
  exact (mul_eq_zero.1 h).resolve_right hℓinv

end

end Riesz1
