/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Lower integrals of power functions on half-lines and quadrants

Calculus used by the small-region estimates of Lemma 5.8. For `s ∈ (0, 1)`:

* `lintegral_Ioi_add_left`: a shift of the variable on a half-line,
  `∫⁻_{v > b} f(u + v) dv = ∫⁻_{w > u + b} f(w) dw`.
* `lintegral_Ioi_rpow`: `∫⁻_{x > c} x^e dx = c^{e+1}/(-(e+1))` for `e < -1` and `c > 0`.
* `lintegral_quadrant_rpow`: the quadrant integral
  `∫⁻_{u > a} ∫⁻_{v > b} (u + v)^{-s-3} = (a + b)^{-s-1} / ((s+1)(s+2))` for `a, b > 0`.

The quadrant integral depends on `a` and `b` only through `a + b`: this is what makes the
small-region pair estimate `d^{-s}` for a pair at distance `d`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Riesz1

/-- A shift of the variable on a half-line: `∫⁻_{v ∈ (b, ∞)} f(u + v) = ∫⁻_{w ∈ (u + b, ∞)} f(w)`. -/
theorem lintegral_Ioi_add_left (f : ℝ → ℝ≥0∞) (u b : ℝ) :
    ∫⁻ v in Ioi b, f (u + v) = ∫⁻ w in Ioi (u + b), f w := by
  rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioi]
  have hpt : ∀ v : ℝ, (Ioi b).indicator (fun v => f (u + v)) v
      = (Ioi (u + b)).indicator f (u + v) := by
    intro v
    simp only [Set.indicator_apply, Set.mem_Ioi]
    by_cases h : b < v
    · have h' : u + b < u + v := by linarith
      rw [ite_eq_left h, ite_eq_left h']
    · have h' : ¬ u + b < u + v := by intro h''; apply h; linarith
      rw [ite_eq_right h, ite_eq_right h']
  simp_rw [hpt]
  exact lintegral_add_left_eq_self (fun w => (Ioi (u + b)).indicator f w) u

/-- The lower integral of a negative power on a half-line: for `e < -1` and `c > 0`,
`∫⁻_{x > c} x^e = c^{e+1} / (-(e+1))`. -/
theorem lintegral_Ioi_rpow {c e : ℝ} (hc : 0 < c) (he : e < -1) :
    ∫⁻ x in Ioi c, ENNReal.ofReal (x ^ e) = ENNReal.ofReal (-(c ^ (e + 1)) / (e + 1)) := by
  have hint : IntegrableOn (fun x : ℝ => x ^ e) (Ioi c) := integrableOn_Ioi_rpow_of_lt he hc
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi c)] fun x : ℝ => x ^ e := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun x hx => ?_)
    exact Real.rpow_nonneg (hc.trans hx).le e
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_Ioi_rpow_of_lt he hc]

/-- **Quadrant integral.** For `a, b > 0` and `0 < s < 1`, the integral of `(u + v)^{-s-3}` over
the quadrant `u > a`, `v > b` depends only on `a + b`:
`∫⁻_{u > a} ∫⁻_{v > b} (u + v)^{-s-3} = (a + b)^{-s-1} / ((s+1)(s+2))`. -/
theorem lintegral_quadrant_rpow {s : ℝ} (hs0 : 0 < s) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫⁻ u in Ioi a, ∫⁻ v in Ioi b, ENNReal.ofReal ((u + v) ^ (-s - 3))
      = ENNReal.ofReal ((a + b) ^ (-s - 1) / ((s + 1) * (s + 2))) := by
  have hinner : ∀ u ∈ Ioi a, ∫⁻ v in Ioi b, ENNReal.ofReal ((u + v) ^ (-s - 3))
      = ENNReal.ofReal (1 / (s + 2)) * ENNReal.ofReal ((u + b) ^ (-s - 2)) := by
    intro u hu
    have hu0 : 0 < u := lt_trans ha (mem_Ioi.mp hu)
    have hub : 0 < u + b := by linarith
    have h1 : ∫⁻ v in Ioi b, ENNReal.ofReal ((u + v) ^ (-s - 3))
        = ∫⁻ w in Ioi (u + b), ENNReal.ofReal (w ^ (-s - 3)) :=
      lintegral_Ioi_add_left (fun w => ENNReal.ofReal (w ^ (-s - 3))) u b
    rw [h1, lintegral_Ioi_rpow hub (by linarith), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have e : (-s - 3 + 1) = -s - 2 := by ring
    rw [e, show (-s - 2 : ℝ) = -(s + 2) by ring, neg_div_neg_eq]
    ring
  rw [setLIntegral_congr_fun measurableSet_Ioi hinner]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have h2 : ∫⁻ u in Ioi a, ENNReal.ofReal ((u + b) ^ (-s - 2))
      = ∫⁻ w in Ioi (b + a), ENNReal.ofReal (w ^ (-s - 2)) := by
    rw [← lintegral_Ioi_add_left (fun w => ENNReal.ofReal (w ^ (-s - 2))) b a]
    refine setLIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    show ENNReal.ofReal ((u + b) ^ (-s - 2)) = ENNReal.ofReal ((b + u) ^ (-s - 2))
    rw [add_comm]
  rw [h2, lintegral_Ioi_rpow (by linarith) (by linarith)]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have e : (-s - 2 + 1) = -s - 1 := by ring
  rw [e, show b + a = a + b from add_comm b a, show (-s - 1 : ℝ) = -(s + 1) by ring,
    neg_div_neg_eq]
  have hs1 : s + 1 ≠ 0 := (by linarith : (0 : ℝ) < s + 1).ne'
  have hs2 : s + 2 ≠ 0 := (by linarith : (0 : ℝ) < s + 2).ne'
  field_simp

end Riesz1

end
end
