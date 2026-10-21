/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.UnitCellIntegral

/-!
# Endpoint errors for interval quadrature

Moving both endpoints of an interval changes its integral by at most the
sum of the two endpoint displacements times a bound on the integrand there.
-/

public section

open MeasureTheory Set

namespace Riesz1

/-- An integral comparison which allows the endpoint strips to have either orientation. -/
theorem abs_integral_sub_integral_le_endpoints {f : ℝ → ℝ} {a b c d B : ℝ}
    (hab : IntervalIntegrable f volume a b) (hcd : IntervalIntegrable f volume c d)
    (hac : IntervalIntegrable f volume a c)
    (hleft : ∀ u ∈ uIcc a c, |f u| ≤ B)
    (hright : ∀ u ∈ uIcc b d, |f u| ≤ B) :
    |(∫ u in a..b, f u) - ∫ u in c..d, f u| ≤ B * (|c - a| + |d - b|) := by
  rw [intervalIntegral.integral_interval_sub_interval_comm hab hcd hac]
  apply (abs_sub _ _).trans
  have hl := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := f) (a := a) (b := c) (C := B)
    (fun u hu => by simpa only [Real.norm_eq_abs] using hleft u (uIoc_subset_uIcc hu))
  have hr := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := f) (a := b) (b := d) (C := B)
    (fun u hu => by simpa only [Real.norm_eq_abs] using hright u (uIoc_subset_uIcc hu))
  simp only [Real.norm_eq_abs] at hl hr
  nlinarith

end Riesz1
