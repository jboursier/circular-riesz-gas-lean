/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # Convexity of negative powers on their positive carrier -/

public section

open Set

namespace Riesz1

/-- A negative power is convex on the positive half-line. -/
theorem convexOn_rpow_neg_Ioi {p : ℝ} (hp : 0 < p) :
    ConvexOn ℝ (Ioi (0 : ℝ)) (fun x => x ^ (-p)) := by
  refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioi _)
    (fun x hx => (Real.hasDerivAt_rpow_const (p := -p) (Or.inl hx.ne')).continuousAt.continuousWithinAt)
    (f' := fun x => -p * x ^ (-p - 1))
    (f'' := fun x => (-p) * (-p - 1) * x ^ (-p - 1 - 1))
    (fun x hx => (Real.hasDerivAt_rpow_const (p := -p) (Or.inl
      (show 0 < x by simpa using hx).ne')).hasDerivWithinAt)
    (fun x hx => by
      have h := (Real.hasDerivAt_rpow_const (p := -p - 1) (Or.inl
        (show 0 < x by simpa using hx).ne')).const_mul (-p)
      have h' : HasDerivAt (fun x : ℝ => -p * x ^ (-p - 1))
          (-p * (-p - 1) * x ^ (-p - 1 - 1)) x := by
        simpa only [mul_assoc] using h
      exact h'.hasDerivWithinAt) ?_
  intro x hx
  exact mul_nonneg (mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith))
    (Real.rpow_nonneg (show 0 ≤ x from (show 0 < x by simpa using hx).le) _)

end Riesz1

end
