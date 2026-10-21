/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.GeometryRelabelAdmissible
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The ground-state potential and its boundary lower bound

Derivatives are taken only at interior chamber points.
-/

@[expose] public section

noncomputable section

open Set
open scoped ContDiff

namespace Riesz1

variable {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c)

/-- The Schrödinger potential `|∇H|²/4 - ΔH/2` of the ground-state transform. -/
def hsGroundStatePotential (x : HsEuclidean N) : ℝ :=
  ‖gradient (hsPairExpression χ) x‖ ^ 2 / 4 - Laplacian.laplacian (hsPairExpression χ) x / 2

/-- Convex pair potentials make every diagonal Hessian entry nonnegative. -/
theorem hsPairExpression_hessian_nonnegative (hc : 0 < c)
    {x : HsEuclidean N} (hx : x ∈ hsChamber N) (v : HsEuclidean N) :
    0 ≤ fderiv ℝ (fderiv ℝ (hsPairExpression χ)) x v v := by
  rw [hessian_hsPairExpression_self χ hx]
  apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (hc.le.trans
    (χ.curvature i j (Finset.mem_filter.mp hj).2 _
      (hsChamber_separation_mem hx (Finset.mem_filter.mp hj).2))) (sq_nonneg _)

/-- The Laplacian of an admissible pair Hamiltonian is nonnegative. -/
theorem hsPairExpression_laplacian_nonnegative (hc : 0 < c)
    {x : HsEuclidean N} (hx : x ∈ hsChamber N) :
    0 ≤ Laplacian.laplacian (hsPairExpression χ) x := by
  rw [laplacian_eq_sum_fderiv_fderiv _ (EuclideanSpace.basisFun (Fin (N : ℕ)) ℝ)]
  exact Finset.sum_nonneg fun _ _ => hsPairExpression_hessian_nonnegative χ hc hx _

/-- The potential is smooth at every interior point. -/
theorem contDiffOn_hsGroundStatePotential :
    ContDiffOn ℝ ∞ (hsGroundStatePotential χ) (hsChamber N) := by
  have hH := hsPairExpression_contDiffOn χ
  have hd := hH.fderiv_of_isOpen (isOpen_hsChamber N) (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)
  have hdd := hd.fderiv_of_isOpen (isOpen_hsChamber N) (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)
  have hg : ContDiffOn ℝ ∞ (fun x => gradient (hsPairExpression χ) x) (hsChamber N) := by
    exact (InnerProductSpace.toDual ℝ (HsEuclidean N)).symm.contDiff.comp_contDiffOn hd
  have hl : ContDiffOn ℝ ∞ (Laplacian.laplacian (hsPairExpression χ)) (hsChamber N) := by
    have he := funext (laplacian_eq_sum_fderiv_fderiv (hsPairExpression χ)
      (EuclideanSpace.basisFun (Fin (N : ℕ)) ℝ))
    rw [he]
    apply ContDiffOn.sum
    intro i _
    exact (hdd.clm_apply contDiffOn_const).clm_apply contDiffOn_const
  exact ((hg.norm_sq ℝ).div_const 4).sub (hl.div_const 2)

/-- Admissibility implies the inverse-square barrier for the transformed potential. -/
theorem hsGroundStatePotential_boundary_lower {C_N : ℝ} (hadm : HsAdmissible χ C_N)
    {x : HsEuclidean N} (hx : x ∈ hsChamber N) :
    (hsBoundaryDistance N hadm.choose x)⁻¹ ^ 2 - C_N ≤ hsGroundStatePotential χ x := by
  obtain ⟨hN, hc, _, hb⟩ := hadm
  have hden : (4 : ℝ) ≤ 4 * (N : ℝ) := by
    have hp : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast N.pos
    linarith
  have hdiv := div_le_div_of_nonneg_left
    (sq_nonneg ‖gradient (hsPairExpression χ) x‖) (by norm_num : (0 : ℝ) < 4) hden
  exact (hb x hx).trans (sub_le_sub_right hdiv _)

/-- In particular the transformed potential is bounded below on the whole chamber. -/
theorem hsGroundStatePotential_lower {C_N : ℝ} (hadm : HsAdmissible χ C_N)
    {x : HsEuclidean N} (hx : x ∈ hsChamber N) :
    -C_N ≤ hsGroundStatePotential χ x := by
  have hb := hsGroundStatePotential_boundary_lower χ hadm hx
  linarith [sq_nonneg ((hsBoundaryDistance N hadm.choose x)⁻¹)]

end Riesz1
