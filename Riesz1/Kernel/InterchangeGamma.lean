/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Tactic

/-!
# Reciprocal-time Gamma integral

For `α > 0` and `c > 0`, the integral of `t ^ (-1 - α) * exp (-c / t)` over `(0, ∞)` equals
`c ^ (-α) * Γ(α)`. The substitution `u = 1 / t` turns it into the Gamma integral
`∫_{(0,∞)} u ^ (α - 1) e^{-cu} du`, which Mathlib evaluates.

This integral supplies the time integrals of the interchange lemma in the proof of Lemma 2.1,
and its integrability follows from its nonzero value.

Main results:
* `Riesz1.integral_rpow_neg_exp_div_Ioi`: the value of the reciprocal-time Gamma integral.
* `Riesz1.integrableOn_rpow_neg_exp_div_Ioi`: the integrand is integrable on `(0, ∞)`.
-/

public section

open MeasureTheory Set Filter Topology

namespace Riesz1

/-- The reciprocal-time Gamma integral `∫_{(0,∞)} t ^ (-1 - α) e^{-c/t} dt = c ^ (-α) Γ(α)`
for `α > 0` and `c > 0`. -/
theorem integral_rpow_neg_exp_div_Ioi {α c : ℝ} (hα : 0 < α) (hc : 0 < c) :
    ∫ t in Ioi (0 : ℝ), t ^ (-1 - α) * Real.exp (-c / t) = c ^ (-α) * Real.Gamma α := by
  -- The substitution `u = t ^ (-1)` applied to `g u = u ^ (α - 1) e^{-cu}`.
  set g : ℝ → ℝ := fun u => u ^ (α - 1) * Real.exp (-(c * u)) with hg
  have hsub := integral_comp_rpow_Ioi g (p := -1) (by norm_num)
  have hpt : ∀ t ∈ Ioi (0 : ℝ),
      (|(-1 : ℝ)| * t ^ ((-1 : ℝ) - 1)) • g (t ^ (-1 : ℝ)) =
        t ^ (-1 - α) * Real.exp (-c / t) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have hpow : t ^ ((-1 : ℝ) - 1) * t ^ (-(α - 1)) = t ^ (-1 - α) := by
      rw [← Real.rpow_add ht0]
      congr 1
      ring
    rw [smul_eq_mul, abs_neg, abs_one, one_mul, hg]
    simp only
    rw [Real.rpow_neg_one, Real.inv_rpow ht0.le, ← Real.rpow_neg ht0.le, ← mul_assoc, hpow]
    rw [show -(c * t⁻¹) = -c / t by ring]
  have hL : ∫ t in Ioi (0 : ℝ), (|(-1 : ℝ)| * t ^ ((-1 : ℝ) - 1)) • g (t ^ (-1 : ℝ)) =
      ∫ t in Ioi (0 : ℝ), t ^ (-1 - α) * Real.exp (-c / t) :=
    setIntegral_congr_fun measurableSet_Ioi hpt
  have hR : ∫ y in Ioi (0 : ℝ), g y = (1 / c) ^ α * Real.Gamma α := by
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi hα hc
    simpa only [hg] using h
  rw [← hL, hsub, hR, one_div, Real.inv_rpow hc.le, Real.rpow_neg hc.le]

/-- The reciprocal-time integrand `t ^ (-1 - α) e^{-c/t}` is integrable on `(0, ∞)` for
`α > 0` and `c > 0`, because its integral is nonzero. -/
theorem integrableOn_rpow_neg_exp_div_Ioi {α c : ℝ} (hα : 0 < α) (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => t ^ (-1 - α) * Real.exp (-c / t)) (Ioi 0) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_rpow_neg_exp_div_Ioi hα hc]
  exact mul_ne_zero (Real.rpow_pos_of_pos hc _).ne' (Real.Gamma_pos_of_pos hα).ne'

end Riesz1
