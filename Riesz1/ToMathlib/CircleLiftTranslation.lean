/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Smoothness and two derivatives at different lifts of one circle point -/

public section

open scoped ContDiff

namespace Riesz1

/-- Equal points on the circle give translated, identical real lifts. -/
theorem circle_lift_translation {L : ℝ} (ψ : AddCircle L → ℝ) {x y : ℝ}
    (hxy : (x : AddCircle L) = (y : AddCircle L)) :
    (fun t : ℝ => ψ (((x - y) + t : ℝ) : AddCircle L)) =
      (fun t : ℝ => ψ (t : AddCircle L)) := by
  funext t
  congr 1
  rw [QuotientAddGroup.mk_add, QuotientAddGroup.mk_sub, hxy, sub_self, zero_add]

/-- Smoothness of a lift is independent of the real representative. -/
theorem contDiffAt_circle_lift_of_coe_eq {L : ℝ} (ψ : AddCircle L → ℝ)
    {n : WithTop ℕ∞} {x y : ℝ} (hxy : (x : AddCircle L) = (y : AddCircle L))
    (hx : ContDiffAt ℝ n (fun t : ℝ => ψ (t : AddCircle L)) x) :
    ContDiffAt ℝ n (fun t : ℝ => ψ (t : AddCircle L)) y := by
  have hx' : ContDiffAt ℝ n (fun t : ℝ => ψ (t : AddCircle L)) ((x - y) + y) := by
    simpa only [sub_add_cancel] using hx
  have hcomp := hx'.comp y
    ((contDiffAt_const (c := x - y)).add (contDiffAt_id (x := y)))
  change ContDiffAt ℝ n (fun t : ℝ => ψ (((x - y) + t : ℝ) : AddCircle L)) y at hcomp
  rwa [circle_lift_translation ψ hxy] at hcomp

/-- Two classical derivatives of a lift are independent of its real representative. -/
theorem deriv_deriv_circle_lift_eq_of_coe_eq {L : ℝ} (ψ : AddCircle L → ℝ)
    {x y : ℝ} (hxy : (x : AddCircle L) = (y : AddCircle L)) :
    deriv (deriv (fun t : ℝ => ψ (t : AddCircle L))) x =
      deriv (deriv (fun t : ℝ => ψ (t : AddCircle L))) y := by
  let F := fun t : ℝ => ψ (t : AddCircle L)
  have heq := circle_lift_translation ψ hxy
  have hd : (fun t : ℝ => deriv F ((x - y) + t)) = deriv F := by
    funext t
    have ht := congrArg (fun f : ℝ → ℝ => deriv f t) heq
    change deriv (fun t : ℝ => F ((x - y) + t)) t = deriv F t at ht
    rw [deriv_comp_const_add] at ht
    exact ht
  have hd2 := congrArg (fun f : ℝ → ℝ => deriv f y) hd
  rw [deriv_comp_const_add] at hd2
  simpa only [sub_add_cancel] using hd2

end Riesz1
