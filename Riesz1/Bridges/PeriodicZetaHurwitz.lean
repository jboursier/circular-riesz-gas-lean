/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Frozen.PeriodicZeta
public import Riesz1.ToMathlib.HurwitzKernel.Derivatives

/-!
# Bridge: the periodic zeta combination as a difference of Hurwitz kernels

The object is `periodicZeta`. The project kernel `hurwitzKernel s x = 2 Re ζ(x, s)` of
`Riesz1/ToMathlib/HurwitzKernel/Derivatives.lean` gives the same combination, since `gradKernelH`
is built on it.

Main result: `periodicZeta_eq_hurwitzKernel_sub`.
-/

public section

namespace Riesz1

/-- The periodic zeta combination equals the Hurwitz kernel at the point `x` minus its value at
`0`: `periodicZeta s x = hurwitzKernel (-s) x - hurwitzKernel (-s) 0`. Both sides are
`2 (Re ζ(x, -s) - Re ζ(0, -s))`. -/
theorem periodicZeta_eq_hurwitzKernel_sub (s : RieszExponent) (x : ℝ) :
    periodicZeta s (x : UnitAddCircle) = hurwitzKernel (-s.val) x - hurwitzKernel (-s.val) 0 := by
  unfold periodicZeta hurwitzKernel
  simp only [Complex.ofReal_neg, AddCircle.coe_zero]
  ring

end Riesz1

end
