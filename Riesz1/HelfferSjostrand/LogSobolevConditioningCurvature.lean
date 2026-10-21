/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Curvature of Gaussian convex perturbations

A smooth convex function has nonnegative second directional derivatives. Adding the
Gaussian quadratic therefore supplies exactly the curvature required by Bakry–Émery.
-/

public section

open Set
open scoped ContDiff InnerProductSpace

namespace Riesz1.LogSobolevInternal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Hessian of a smooth convex function is nonnegative on the diagonal. -/
lemma convex_hessian_nonneg {B : E → ℝ} (hB : ContDiff ℝ ∞ B)
    (hc : ConvexOn ℝ univ B) (x h : E) :
    0 ≤ (fderiv ℝ (fderiv ℝ B) x h) h := by
  have hd : Differentiable ℝ B := hB.differentiable (by simp)
  have hd₂ : Differentiable ℝ (fderiv ℝ B) :=
    (hB.fderiv_right (m := 1) (by simp)).differentiable (by simp)
  let l : ℝ → E := fun t => x + t • h
  have hl (t : ℝ) : HasDerivAt l h t := by
    simpa [l] using (hasDerivAt_id t).smul_const h |>.const_add x
  have hBc : ConvexOn ℝ univ (fun t => B (l t)) := by
    refine ⟨convex_univ, fun u _ v _ s t hs ht hst => ?_⟩
    have hh := hc.2 (mem_univ (l u)) (mem_univ (l v)) hs ht hst
    have he : l (s * u + t * v) = s • l u + t • l v := by
      have htdef : t = 1 - s := by linarith
      rw [htdef]
      dsimp [l]
      module
    simpa only [smul_eq_mul, he] using hh
  have hBd (t : ℝ) : HasDerivAt (fun t => B (l t)) (fderiv ℝ B (l t) h) t :=
    (hd (l t)).hasFDerivAt.comp_hasDerivAt t (hl t)
  have hm : Monotone (fun t => (fderiv ℝ B (l t)) h) := by
    have hm' := hBc.monotoneOn_deriv (fun t _ => (hBd t).differentiableAt)
    simpa only [monotoneOn_univ, funext (fun t => (hBd t).deriv)] using hm'
  have hdd := ((hd₂ (l 0)).hasFDerivAt.comp_hasDerivAt 0 (hl 0)).clm_apply
    (hasDerivAt_const 0 h)
  have hdd' : HasDerivAt (fun t => (fderiv ℝ B (l t)) h)
      ((fderiv ℝ (fderiv ℝ B) x h) h) 0 := by
    simpa [l] using hdd
  rw [← hdd'.deriv]
  exact hm.deriv_nonneg

/-- The Hessian of the Gaussian quadratic. -/
lemma gaussian_quadratic_hessian (w : ℝ) (x h : E) :
    (fderiv ℝ (fderiv ℝ (fun y : E => (2 * w)⁻¹ * ‖y‖ ^ 2)) x h) h =
      w⁻¹ * ‖h‖ ^ 2 := by
  have he : fderiv ℝ (fun y : E => (2 * w)⁻¹ * ‖y‖ ^ 2) =
      fun y => (2 * w)⁻¹ • ((2 : ℕ) • innerSL ℝ y) := by
    funext y
    have hs : DifferentiableAt ℝ (fun z : E => ‖z‖ ^ 2) y := by
      simpa only [id_eq] using (differentiableAt_id (𝕜 := ℝ) (x := y)).norm_sq ℝ
    rw [fderiv_const_mul hs, fderiv_norm_sq_apply]
  rw [he]
  have hd := ((innerSL ℝ (E := E)).hasFDerivAt (x := x)).const_smul (2 : ℕ)
  have hd' := hd.const_smul ((2 * w)⁻¹)
  have he' : HasFDerivAt (fun y : E => (2 * w)⁻¹ • ((2 : ℕ) • innerSL ℝ y))
      ((2 * w)⁻¹ • (2 : ℕ) • innerSL ℝ) x := by
    exact hd'
  rw [he'.fderiv]
  have hinner : (innerSL ℝ (E := E)) h h = ‖h‖^2 := by
    rw [innerSL_apply_apply, real_inner_self_eq_norm_sq]
  simp only [two_smul, smul_apply, add_apply, smul_eq_mul]
  ring_nf
  rw [hinner]

/-- A smooth convex perturbation of the Gaussian has curvature at least `w⁻¹`. -/
lemma gaussian_convex_hessian (w : ℝ) {B : E → ℝ} (hB : ContDiff ℝ ∞ B)
    (hc : ConvexOn ℝ univ B) (x h : E) :
    w⁻¹ * ‖h‖ ^ 2 ≤
      (fderiv ℝ (fderiv ℝ (fun y : E => (2 * w)⁻¹ * ‖y‖ ^ 2 + B y)) x h) h := by
  have hQ : ContDiff ℝ ∞ (fun y : E => (2 * w)⁻¹ * ‖y‖ ^ 2) :=
    contDiff_const.mul (contDiff_id.norm_sq ℝ)
  have he : fderiv ℝ (fun y : E => (2 * w)⁻¹ * ‖y‖ ^ 2 + B y) =
      fderiv ℝ (fun y : E => (2 * w)⁻¹ * ‖y‖ ^ 2) + fderiv ℝ B := by
    funext y
    exact fderiv_fun_add (hQ.differentiable (by simp) y) (hB.differentiable (by simp) y)
  rw [he, fderiv_add ((hQ.fderiv_right (m := 1) (by simp)).differentiable
    (by simp) x) ((hB.fderiv_right (m := 1) (by simp)).differentiable (by simp) x)]
  simp only [add_apply, gaussian_quadratic_hessian]
  exact le_add_of_nonneg_right (convex_hessian_nonneg hB hc x h)

end Riesz1.LogSobolevInternal
