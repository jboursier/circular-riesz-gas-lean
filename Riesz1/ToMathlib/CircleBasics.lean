/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Fourier.AddCircle

/-!
# Elementary facts on periodic functions and circle characters

* `deriv_periodic_of`: the derivative of a periodic function has the same period.
* `norm_fourier_apply`: the characters `fourier n` of the unit circle have norm one.
-/

@[expose] public section

namespace Riesz1

/-- The derivative of a function with period `p` has period `p`. -/
lemma deriv_periodic_of {ψ : ℝ → ℝ} {p : ℝ} (hp : Function.Periodic ψ p) :
    Function.Periodic (deriv ψ) p := by
  intro x
  have h1 : (fun y => ψ (y + p)) = ψ := funext fun y => hp y
  have h2 := deriv_comp_add_const (f := ψ) (a := p) x
  rw [h1] at h2
  exact h2.symm

/-- Every character of the circle has modulus one at every point. -/
lemma norm_fourier_apply (n : ℤ) (z : UnitAddCircle) : ‖fourier n z‖ = 1 := by
  rw [fourier_apply, Circle.norm_coe]

end Riesz1

end
