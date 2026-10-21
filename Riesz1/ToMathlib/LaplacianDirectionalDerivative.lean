/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-! # The Laplacian and directional differentiation

Classical smooth directional derivatives commute. Taking a finite orthonormal
trace then commutes a directional derivative with the Euclidean Laplacian.
-/

@[expose] public section

noncomputable section

open InnerProductSpace
open scoped ContDiff Laplacian

namespace Riesz1

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem fderiv_direction_commute {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ f y v) x w =
      fderiv ℝ (fun y => fderiv ℝ f y w) x v := by
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  rw [fderiv_clm_apply (hd x) (differentiableAt_const v),
    fderiv_clm_apply (hd x) (differentiableAt_const w)]
  simpa using (hf.contDiffAt (x := x)).isSymmSndFDerivAt (by simp) w v

theorem fderiv_direction_third_commute {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => fderiv ℝ f z v) y w) x w =
      fderiv ℝ (fun y => fderiv ℝ (fun z => fderiv ℝ f z w) y w) x v := by
  have he : (fun y => fderiv ℝ (fun z => fderiv ℝ f z v) y w) =
      fun y => fderiv ℝ (fun z => fderiv ℝ f z w) y v :=
    funext fun y => fderiv_direction_commute hf y v w
  rw [he]
  exact fderiv_direction_commute ((hf.fderiv_right (by simp)).clm_apply contDiff_const) x v w

variable [FiniteDimensional ℝ E]

theorem laplacian_eq_sum_fderiv_direction {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    {ι : Type*} [Fintype ι] (B : OrthonormalBasis ι ℝ E) (x : E) :
    Δ f x = ∑ i, fderiv ℝ (fun y => fderiv ℝ f y (B i)) x (B i) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f B]
  apply Finset.sum_congr rfl
  intro i _
  rw [fderiv_clm_apply ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x)
    (differentiableAt_const (B i)), iteratedFDeriv_two_apply]
  simp

theorem laplacian_fderiv_direction {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (x v : E) :
    Δ (fun y => fderiv ℝ f y v) x = fderiv ℝ (Δ f) x v := by
  let B := stdOrthonormalBasis ℝ E
  have htrace : Δ f = fun x => ∑ i,
      fderiv ℝ (fun y => fderiv ℝ f y (B i)) x (B i) :=
    funext (laplacian_eq_sum_fderiv_direction hf B)
  rw [laplacian_eq_sum_fderiv_direction
    ((hf.fderiv_right (by simp)).clm_apply contDiff_const) B x, htrace]
  have hd (i) : DifferentiableAt ℝ
      (fun x => fderiv ℝ (fun y => fderiv ℝ f y (B i)) x (B i)) x :=
    (((((hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).fderiv_right
      (m := ∞) (by simp)).clm_apply
      contDiff_const).differentiable (by simp)) x
  rw [fderiv_fun_sum (fun i _ => hd i), sum_apply]
  exact Finset.sum_congr rfl fun i _ => fderiv_direction_third_commute hf x v (B i)

end Riesz1
