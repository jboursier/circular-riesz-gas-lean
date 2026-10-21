/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.LaplacianDirectionalDerivative
public import Riesz1.ToMathlib.PeriodizationLaplacian
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # The smooth Langevin commutator

Directional differentiation of `∇H · ∇f - Δf` produces the Hessian of
`H` applied to the direction and `∇f`. Only local smoothness of `H` is needed.
-/

@[expose] public section

noncomputable section

open InnerProductSpace
open scoped ContDiff Laplacian

namespace Riesz1

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem differentiableAt_gradient_of_fderiv {H : E → ℝ} {x : E}
    (hH : DifferentiableAt ℝ (fderiv ℝ H) x) : DifferentiableAt ℝ (gradient H) x :=
  (toDual ℝ E).symm.toContinuousLinearEquiv.differentiableAt.comp x hH

theorem inner_fderiv_gradient {H : E → ℝ} {x : E}
    (hH : DifferentiableAt ℝ (fderiv ℝ H) x) (v w : E) :
    inner ℝ (fderiv ℝ (gradient H) x v) w = fderiv ℝ (fderiv ℝ H) x v w := by
  have hd : fderiv ℝ (gradient H) x =
      (toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (fderiv ℝ (fderiv ℝ H) x) := by
    exact (((toDual ℝ E).symm.toContinuousLinearEquiv.hasFDerivAt).comp x
      hH.hasFDerivAt).fderiv
  rw [hd]
  change inner ℝ ((toDual ℝ E).symm (fderiv ℝ (fderiv ℝ H) x v)) w = _
  exact congrArg (fun l : StrongDual ℝ E => l w) ((toDual ℝ E).apply_symm_apply _)

theorem fderiv_gradient_eq_gradient_direction {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (x v : E) :
    fderiv ℝ (gradient f) x v = gradient (fun y => fderiv ℝ f y v) x := by
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  apply ext_inner_right ℝ
  intro w
  rw [inner_fderiv_gradient hdf, inner_gradient_left]
  rw [fderiv_clm_apply hdf (differentiableAt_const v)]
  simpa using (hf.contDiffAt (x := x)).isSymmSndFDerivAt (by simp) v w

/-- Classical directional commutator for a smooth potential and smooth test. -/
theorem langevin_direction_commutator {H f : E → ℝ} {x : E}
    (hH : ContDiffAt ℝ ∞ H x) (hf : ContDiff ℝ ∞ f) (v : E) :
    fderiv ℝ (fun y => inner ℝ (gradient H y) (gradient f y) - Δ f y) x v -
      (inner ℝ (gradient H x) (gradient (fun y => fderiv ℝ f y v) x) -
        Δ (fun y => fderiv ℝ f y v) x) =
      fderiv ℝ (fderiv ℝ H) x v (gradient f x) := by
  have hdH : DifferentiableAt ℝ (fderiv ℝ H) x :=
    (hH.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  have hgH := differentiableAt_gradient_of_fderiv hdH
  have hgf := differentiableAt_gradient_of_fderiv hdf
  have hΔ : DifferentiableAt ℝ (Δ f) x := (contDiff_laplacian hf).differentiable (by simp) x
  rw [fderiv_fun_sub (hgH.inner ℝ hgf) hΔ, sub_apply, fderiv_inner_apply ℝ hgH hgf,
    inner_fderiv_gradient hdH, fderiv_gradient_eq_gradient_direction hf,
    laplacian_fderiv_direction hf]
  ring

end Riesz1
