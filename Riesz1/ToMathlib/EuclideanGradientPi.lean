/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-!
# Coordinates of a Euclidean gradient after changing the norm on a product

The Euclidean gradient of a function originally defined on a finite real
product evaluates to its original differential on coordinate unit vectors.
-/

public section

noncomputable section

namespace Riesz1

theorem gradient_comp_ofLp_apply {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    {y : EuclideanSpace ℝ (Fin n)} (hf : DifferentiableAt ℝ f (WithLp.ofLp y)) (i : Fin n) :
    gradient (fun z : EuclideanSpace ℝ (Fin n) => f (WithLp.ofLp z)) y i =
      fderiv ℝ f (WithLp.ofLp y) (Pi.single i 1) := by
  let L := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)
  have hd := hf.hasFDerivAt.comp y L.hasFDerivAt
  have he := hd.differentiableAt.hasGradientAt.fderiv_apply (y := EuclideanSpace.single i 1)
  have hi : inner ℝ (gradient (fun z => f (WithLp.ofLp z)) y)
      (EuclideanSpace.single i 1) = gradient (fun z => f (WithLp.ofLp z)) y i := by
    rw [EuclideanSpace.inner_single_right]
    simp only [RCLike.conj_to_real, one_mul]
  change fderiv ℝ (fun z : EuclideanSpace ℝ (Fin n) => f (WithLp.ofLp z)) y
    (EuclideanSpace.single i 1) = inner ℝ (gradient (fun z => f (WithLp.ofLp z)) y)
      (EuclideanSpace.single i 1) at he
  have hdEq := hd.fderiv
  change fderiv ℝ (fun z : EuclideanSpace ℝ (Fin n) => f (WithLp.ofLp z)) y = _ at hdEq
  rw [hi, hdEq] at he
  exact he.symm

end Riesz1

end
