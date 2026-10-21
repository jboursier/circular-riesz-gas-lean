/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.HurwitzKernel.EndpointEstimates

/-!
# Curvature terms of the Hurwitz kernel

The second derivative of the Hurwitz kernel `g_s` (`hurwitzKernel s`) on `(0, 1)` is
`s (s + 1) ∑_{k ∈ ℤ} |r - k|^{-s-2}`. Every summand is nonnegative, so each single term is a lower
bound for the curvature. This file records:

* `hurwitzKernel_curvature_ge_term`: for every integer `k`, the curvature at `r` is at least
  `s (s + 1) |r - k|^{-s-2}`. Taking `k = 0` or `k = 1` gives the Riesz pair curvature at a gap `r`
  and at its complement `1 - r`.
* `hurwitzKernel_curvature_ge_const`: the curvature is at least `s (s + 1) 2^{s+2}` on `(0, 1)`,
  since the nearer of `r` and `1 - r` is at most `1/2`.

These are the inputs for the Hessian lower bound of Lemma 5.2.
-/

@[expose] public section

open Set

namespace Riesz1

/-- The curvature of the Hurwitz kernel at `r ∈ (0, 1)` dominates each summand of the series
`s (s + 1) ∑_{k ∈ ℤ} |r - k|^{-s-2}`. -/
theorem hurwitzKernel_curvature_ge_term (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) {r : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) (k : ℤ) :
    s * (s + 1) * |r - k| ^ (-s - 2) ≤ deriv (deriv (hurwitzKernel s)) r := by
  rw [(hasDerivAt_deriv_hurwitzKernel_unit s hs0 hs1 r hr.1 hr.2).deriv]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hsum := (summable_and_tsum_int_abs_rpow (-s - 2) (by linarith) r hr.1 hr.2).1
  exact hsum.le_tsum k (fun j _ => Real.rpow_nonneg (abs_nonneg _) _)

/-- Every curvature term is nonnegative, so the curvature is nonnegative on `(0, 1)`. -/
theorem hurwitzKernel_curvature_nonneg (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) {r : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) : 0 ≤ deriv (deriv (hurwitzKernel s)) r :=
  (by positivity : (0 : ℝ) ≤ s * (s + 1) * |r - (0 : ℤ)| ^ (-s - 2)).trans
    (hurwitzKernel_curvature_ge_term s hs0 hs1 hr 0)

/-- A uniform lower bound on `(0, 1)`: the curvature is at least `s (s + 1) 2^{s+2}`. The point
`r` lies within `1/2` of `0` or of `1`, and the corresponding summand is at least `2^{s+2}`. -/
theorem hurwitzKernel_curvature_ge_const (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) {r : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) : s * (s + 1) * 2 ^ (s + 2) ≤ deriv (deriv (hurwitzKernel s)) r := by
  have hpow : (1 / 2 : ℝ) ^ (-s - 2) = 2 ^ (s + 2) := by
    rw [show -s - 2 = -(s + 2) by ring, Real.rpow_neg (by norm_num), one_div,
      Real.inv_rpow (by norm_num), inv_inv]
  have hc : 0 ≤ s * (s + 1) := by positivity
  rcases le_total r (1 / 2) with h | h
  · have hle : (1 / 2 : ℝ) ^ (-s - 2) ≤ |r - ((0 : ℤ) : ℝ)| ^ (-s - 2) := by
      rw [Int.cast_zero, sub_zero, abs_of_pos hr.1]
      exact Real.rpow_le_rpow_of_nonpos hr.1 h (by linarith)
    rw [hpow] at hle
    exact (mul_le_mul_of_nonneg_left hle hc).trans
      (hurwitzKernel_curvature_ge_term s hs0 hs1 hr 0)
  · have hle : (1 / 2 : ℝ) ^ (-s - 2) ≤ |r - ((1 : ℤ) : ℝ)| ^ (-s - 2) := by
      rw [Int.cast_one, abs_of_neg (by linarith [hr.2])]
      have h' : 0 < -(r - 1) := by linarith [hr.2]
      exact Real.rpow_le_rpow_of_nonpos h' (by linarith) (by linarith)
    rw [hpow] at hle
    exact (mul_le_mul_of_nonneg_left hle hc).trans
      (hurwitzKernel_curvature_ge_term s hs0 hs1 hr 1)

end Riesz1

end
