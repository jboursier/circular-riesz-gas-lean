/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The ground-state product rule on an open set

Classical differentiation of `exp(t H) f`, including its second
directional derivatives. Only interior smoothness is required.
-/

@[expose] public section

noncomputable section

open Set Filter Topology InnerProductSpace
open scoped ContDiff Laplacian

namespace Riesz1

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- First derivative of an exponentially weighted smooth function. -/
theorem fderiv_exp_mul_apply {U : Set E} (hU : IsOpen U) {H f : E → ℝ}
    (hH : ContDiffOn ℝ ∞ H U) (hf : ContDiffOn ℝ ∞ f U)
    (t : ℝ) {x : E} (hx : x ∈ U) (v : E) :
    fderiv ℝ (fun z => Real.exp (t * H z) * f z) x v =
      Real.exp (t * H x) * (fderiv ℝ f x v + t * fderiv ℝ H x v * f x) := by
  have hHd := (hH.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
  have hfd := (hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
  have hd := (hHd.hasFDerivAt.const_mul t).exp.mul hfd.hasFDerivAt
  change HasFDerivAt (fun z => Real.exp (t * H z) * f z) _ x at hd
  rw [hd.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- Second directional derivative of an exponentially weighted function. -/
theorem fderiv_fderiv_exp_mul_apply {U : Set E} (hU : IsOpen U) {H f : E → ℝ}
    (hH : ContDiffOn ℝ ∞ H U) (hf : ContDiffOn ℝ ∞ f U)
    (t : ℝ) {x : E} (hx : x ∈ U) (v : E) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => Real.exp (t * H z) * f z) y v) x v =
      Real.exp (t * H x) *
        (fderiv ℝ (fun y => fderiv ℝ f y v) x v +
          2 * t * fderiv ℝ H x v * fderiv ℝ f x v +
          (t * fderiv ℝ (fun y => fderiv ℝ H y v) x v +
            t ^ 2 * (fderiv ℝ H x v) ^ 2) * f x) := by
  have hHd := (hH.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
  have hfd := (hf.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num)
  have hHH : ContDiffOn ℝ ∞ (fderiv ℝ H) U := hH.fderiv_of_isOpen hU (by simp)
  have hff : ContDiffOn ℝ ∞ (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
  have hdH : DifferentiableAt ℝ (fun y => fderiv ℝ H y v) x :=
    ((hHH.clm_apply contDiffOn_const).contDiffAt
      (hU.mem_nhds hx)).differentiableAt (by norm_num)
  have hdf : DifferentiableAt ℝ (fun y => fderiv ℝ f y v) x :=
    ((hff.clm_apply contDiffOn_const).contDiffAt
      (hU.mem_nhds hx)).differentiableAt (by norm_num)
  have heq : (fun y => fderiv ℝ (fun z => Real.exp (t * H z) * f z) y v) =ᶠ[𝓝 x]
      (fun y => Real.exp (t * H y) * (fderiv ℝ f y v + t * fderiv ℝ H y v * f y)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact fderiv_exp_mul_apply hU hH hf t hy v
  rw [heq.fderiv_eq]
  have hd := (hHd.hasFDerivAt.const_mul t).exp.mul
    (hdf.hasFDerivAt.add ((hdH.hasFDerivAt.const_mul t).mul hfd.hasFDerivAt))
  change HasFDerivAt
    (fun y => Real.exp (t * H y) * (fderiv ℝ f y v + t * fderiv ℝ H y v * f y)) _ x at hd
  rw [hd.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, Pi.add_apply, Pi.mul_apply]
  ring

variable [FiniteDimensional ℝ E]

/-- The Laplacian product rule for the exponential ground-state weight. -/
theorem laplacian_exp_mul {U : Set E} (hU : IsOpen U) {H f : E → ℝ}
    (hH : ContDiffOn ℝ ∞ H U) (hf : ContDiffOn ℝ ∞ f U)
    (t : ℝ) {x : E} (hx : x ∈ U) :
    Δ (fun z => Real.exp (t * H z) * f z) x = Real.exp (t * H x) *
      (Δ f x + 2 * t * inner ℝ (gradient H x) (gradient f x) +
        (t * Δ H x + t ^ 2 * ‖gradient H x‖ ^ 2) * f x) := by
  let B := stdOrthonormalBasis ℝ E
  have hdiag (g : E → ℝ) (hg : ContDiffOn ℝ ∞ g U) (v : E) :
      iteratedFDeriv ℝ 2 g x ![v, v] =
        fderiv ℝ (fun y => fderiv ℝ g y v) x v := by
    have hgg : ContDiffOn ℝ ∞ (fderiv ℝ g) U := hg.fderiv_of_isOpen hU (by simp)
    rw [fderiv_clm_apply
      ((hgg.contDiffAt (hU.mem_nhds hx)).differentiableAt (by norm_num))
      (differentiableAt_const v), iteratedFDeriv_two_apply]
    simp
  have hs (g : E → ℝ) (hg : ContDiffOn ℝ ∞ g U) :
      Δ g x = ∑ i, fderiv ℝ (fun y => fderiv ℝ g y (B i)) x (B i) := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis g B]
    exact Finset.sum_congr rfl (fun i _ => hdiag g hg (B i))
  have hh : ∑ i, fderiv ℝ H x (B i) * fderiv ℝ f x (B i) =
      inner ℝ (gradient H x) (gradient f x) := by
    rw [← B.sum_inner_mul_inner (gradient H x) (gradient f x)]
    apply Finset.sum_congr rfl
    intro i _
    simp only [inner_gradient_left, inner_gradient_right, RCLike.conj_to_real]
  have hhh : ∑ i, (fderiv ℝ H x (B i)) ^ 2 = ‖gradient H x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq (gradient H x), ← B.sum_inner_mul_inner]
    apply Finset.sum_congr rfl
    intro i _
    simp only [inner_gradient_left, inner_gradient_right, RCLike.conj_to_real]
    ring
  rw [hs _ ((contDiffOn_const.mul hH).exp.mul hf)]
  simp_rw [fderiv_fderiv_exp_mul_apply hU hH hf t hx]
  rw [← Finset.mul_sum]
  congr 1
  rw [hs f hf, hs H hH, ← hh, ← hhh]
  simp only [Finset.mul_sum, Finset.sum_mul, add_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

end Riesz1
