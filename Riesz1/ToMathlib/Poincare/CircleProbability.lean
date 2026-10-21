/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.Poincare.Circle

/-!
# Poincaré for uniform probability on a circle

The normalized version of the circle estimate. The derivative energy is the normalized interval integral.
-/

public section

open MeasureTheory

namespace Riesz1

/-- The uniform probability version of the circle Poincaré inequality. -/
theorem integral_sub_mean_sq_le_haarAddCircle (T : ℝ) [hT : Fact (0 < T)]
    (f : AddCircle T → ℝ) (hf : ContDiff ℝ 1 fun x : ℝ => f (x : AddCircle T)) :
    (∫ t, (f t - ∫ s, f s ∂AddCircle.haarAddCircle) ^ 2 ∂AddCircle.haarAddCircle) ≤
      (T / (2 * Real.pi)) ^ 2 *
        (T⁻¹ * ∫ x in (0 : ℝ)..T, (deriv (fun y : ℝ => f (y : AddCircle T)) x) ^ 2) := by
  rw [AddCircle.integral_haarAddCircle, AddCircle.integral_haarAddCircle]
  simp only [smul_eq_mul]
  have h := mul_le_mul_of_nonneg_left
    (integral_sub_average_sq_le_addCircle T f hf) (inv_nonneg.mpr hT.out.le)
  simpa only [mul_left_comm] using h

end Riesz1
