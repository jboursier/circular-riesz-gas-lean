/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.FiniteMarkDistance
import all Riesz1.ToMathlib.FiniteMarkDistance
public import Mathlib.Tactic

/-!
# Local lower bounds for the capped marked distance

The triangle inequality propagates a lower bound for the capped distance
to a finite nonempty family of marks. This supplies uniform neighborhoods
for local kernel-convolution differentiation.
-/

public section

namespace Riesz1

/-- Moving less than `r-u` from a point of capped marked distance at least
`r` leaves capped distance at least `u`. -/
theorem le_cappedMarkDistance_of_dist {X ι : Type*} [PseudoMetricSpace X]
    [Fintype ι] [Nonempty ι] (marks : ι → X) {x y : X} {r u : ℝ}
    (hu : u ≤ 1) (hr : r ≤ cappedMarkDistance marks x)
    (hd : dist x y ≤ r - u) : u ≤ cappedMarkDistance marks y := by
  unfold cappedMarkDistance
  apply le_min hu
  apply (Finset.le_inf'_iff _ _).mpr
  intro j _
  have h₀ := hr.trans (cappedMarkDistance_le_dist marks x j)
  have h₁ := dist_triangle x y (marks j)
  linarith

end Riesz1
