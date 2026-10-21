/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopArcsDerivs
public import Riesz1.Auxiliary.LoopArcsLambda
public import Riesz1.ToMathlib.TriangleInterval

/-!
# The cutoff `Q` in triangle form

The cutoff `Q = loopArcQ s N` has, for `a, b ≥ 0` with `a + b > 0`, the
indicator representation of `loopArcQ_eq_integral_indicator` in the variables `(x, y)` with
`x = u + v`, `y = u`. This file rewrites it in the variables `(u, v)` of the arc function
`Λ = loopArcLambda`:

`Q(a + b) = ∫₀^R (∫₀^{R-u} -g'''(u + v) 1[a < u] 1[b < v] dv) du
  + g''(R) ∫₀^R 1[a < u] 1[b < R - u] du`,

with `R = N / 2`. The triangle change is `integral_triangle_interval_eq`, and the bound on the
kernel `-g'''(x) 1[a < y] 1[b < x - y]` uses the scaled bound `|g'''(x)| ≤ C x^{-s-3}`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

/-- The derivative of a real function is measurable, so each `k`-th iterated derivative with
`k ≥ 1` is measurable. -/
theorem measurable_iteratedDeriv_succ_real (n : ℕ) (f : ℝ → ℝ) :
    Measurable (iteratedDeriv (n + 1) f) := by
  rw [iteratedDeriv_succ]
  exact measurable_deriv _

/-- **The cutoff `Q` in `(u, v)` form.** For `a, b ≥ 0` with `a + b > 0` and `R = N / 2`,
`Q(a + b)` is the triangle integral of `-g_N'''(u + v) 1[a < u] 1[b < v]` over `u, v > 0`,
`u + v < R`, plus the atom `g_N''(R)` times the one-dimensional integral. -/
theorem loopArcQ_eq_triangle (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (N : ℕ+) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) :
    loopArcQ s N (a + b)
      = (∫ u in (0 : ℝ)..((N : ℝ) / 2), ∫ v in (0 : ℝ)..((N : ℝ) / 2 - u),
          -iteratedDeriv 3 (loopArcG s N) (u + v)
            * ((if a < u then (1 : ℝ) else 0) * (if b < v then (1 : ℝ) else 0)))
        + iteratedDeriv 2 (loopArcG s N) ((N : ℝ) / 2)
          * ∫ u in (0 : ℝ)..((N : ℝ) / 2),
              (if a < u then (1 : ℝ) else 0) * (if b < (N : ℝ) / 2 - u then (1 : ℝ) else 0) := by
  have hR : (0 : ℝ) ≤ (N : ℝ) / 2 := by positivity
  obtain ⟨C, hC, hD⟩ := norm_iteratedDeriv_loopArcG_le s hs0 hs1
  -- The kernel `G(x, y) = -g'''(x) 1[a < y] 1[b < x - y]`.
  set G : ℝ → ℝ → ℝ := fun x y => -iteratedDeriv 3 (loopArcG s N) x
    * ((if a < y then (1 : ℝ) else 0) * (if b < x - y then (1 : ℝ) else 0)) with hG
  have hmeas : Measurable (fun p : ℝ × ℝ => G p.1 p.2) := by
    simp only [hG]
    refine Measurable.mul ?_ (Measurable.mul ?_ ?_)
    · exact (measurable_iteratedDeriv_succ_real 2 _).comp measurable_fst |>.neg
    · exact Measurable.ite (measurableSet_lt measurable_const measurable_snd) measurable_const
        measurable_const
    · exact Measurable.ite (measurableSet_lt measurable_const
        (measurable_fst.sub measurable_snd)) measurable_const measurable_const
  -- Bound: the kernel vanishes unless `x > a + b`, and there `|g'''(x)| ≤ C (a + b)^{-s-3}`.
  have hK : ∀ x y : ℝ, 0 < y → y < x → x ≤ (N : ℝ) / 2 →
      |G x y| ≤ C * (a + b) ^ (-s - 3) := by
    intro x y hy hyx hxR
    have hCnn : 0 ≤ C * (a + b) ^ (-s - 3) := by positivity
    simp only [hG]
    by_cases h : a < y ∧ b < x - y
    · have hxab : a + b < x := by linarith [h.1, h.2]
      have hx0 : 0 < x := by linarith
      have h3 := hD N 3 (by norm_num) (by norm_num) x hx0 hxR
      have hpow : x ^ (-s - ((3 : ℕ) : ℝ)) ≤ (a + b) ^ (-s - ((3 : ℕ) : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) hxab.le (by push_cast; linarith)
      have hcast : (-s - ((3 : ℕ) : ℝ)) = -s - 3 := by push_cast; ring
      rw [hcast] at h3 hpow
      rw [abs_mul, abs_neg, abs_mul]
      simp only [h.1, h.2, ite_true, abs_one, mul_one]
      calc |iteratedDeriv 3 (loopArcG s N) x| ≤ C * x ^ (-s - 3) := h3
        _ ≤ C * (a + b) ^ (-s - 3) := mul_le_mul_of_nonneg_left hpow hC.le
    · -- the indicator product vanishes
      have hprod : (if a < y then (1 : ℝ) else 0) * (if b < x - y then (1 : ℝ) else 0) = 0 := by
        by_cases h1 : a < y
        · have h2 : ¬ (b < x - y) := fun h2 => h ⟨h1, h2⟩
          simp [h1, h2]
        · simp [h1]
      rw [hprod, mul_zero, abs_zero]
      exact hCnn
  -- Triangle change of variables for the first term.
  have hT := integral_triangle_interval_eq hR G hmeas hK
  have hfirst : (∫ x in (0 : ℝ)..((N : ℝ) / 2), -iteratedDeriv 3 (loopArcG s N) x
        * ∫ y in (0 : ℝ)..x, (if a < y then (1 : ℝ) else 0) * (if b < x - y then (1 : ℝ) else 0))
      = ∫ x in (0 : ℝ)..((N : ℝ) / 2), ∫ y in (0 : ℝ)..x, G x y := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [hG]
    rw [intervalIntegral.integral_const_mul]
  rw [loopArcQ_eq_integral_indicator s hs0 hs1 N ha hb hab, hfirst, hT]
  congr 1
  refine intervalIntegral.integral_congr fun u _ => ?_
  refine intervalIntegral.integral_congr fun v _ => ?_
  simp only [hG, add_sub_cancel_left]

end Riesz1

end
end
