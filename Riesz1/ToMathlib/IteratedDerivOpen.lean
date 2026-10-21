/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Riesz1.ToMathlib.CircleBasics

/-!
# Derivatives of even functions, and iterated derivatives on open sets

General calculus facts used by the microscopic loop arcs (`Riesz1/Auxiliary/LoopArcs*.lean`):

* an even function has zero derivative at `0` (`Riesz1.deriv_zero_of_even`).
* iterated derivatives of a function smooth on an open set are smooth there, with the expected
  derivative (`Riesz1.contDiffOn_iteratedDeriv_open`, `Riesz1.hasDerivAt_iteratedDeriv_open`).
-/

@[expose] public section

noncomputable section

open scoped ContDiff

namespace Riesz1

/-- An even function has zero derivative at the origin. -/
theorem deriv_zero_of_even (h : ℝ → ℝ) (he : ∀ y, h (-y) = h y) : deriv h 0 = 0 := by
  have h1 := deriv_comp_neg (f := h) (x := 0)
  have hfun : (fun x => h (-x)) = h := funext he
  rw [hfun, neg_zero] at h1
  linarith

/-- Every iterated derivative of a function that is smooth on an open set is smooth there. -/
theorem contDiffOn_iteratedDeriv_open {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (k : ℕ) : ContDiffOn ℝ ∞ (iteratedDeriv k f) U := by
  induction k with
  | zero => rw [iteratedDeriv_zero]; exact hf
  | succ k ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv_of_isOpen hU (by simp)

/-- On an open set where `f` is smooth, the derivative of `iteratedDeriv k f` is
`iteratedDeriv (k + 1) f`. -/
theorem hasDerivAt_iteratedDeriv_open {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (k : ℕ) {x : ℝ} (hx : x ∈ U) :
    HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f x) x := by
  have hdiff : DifferentiableAt ℝ (iteratedDeriv k f) x :=
    ((contDiffOn_iteratedDeriv_open hU hf k).differentiableOn (by simp)).differentiableAt
      (hU.mem_nhds hx)
  rw [iteratedDeriv_succ]
  exact hdiff.hasDerivAt

end Riesz1

end
end
