/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.LangevinCommutator
public import Riesz1.HelfferSjostrand.GradientConvergence
public import Riesz1.HelfferSjostrand.GradientConvergenceAnchored

/-!
# The pointwise commutator on both source domains

The coordinate commutator assertions of
Proposition 3.1. All derivative expressions are
the Euclidean derivatives of the Hamiltonians on their interiors.
-/

public section

noncomputable section

open MeasureTheory InnerProductSpace
open scoped ContDiff Laplacian

namespace Riesz1

theorem hsCommutator_linear_coordinates {n : ℕ}
    (l : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (a : EuclideanSpace ℝ (Fin n)) :
    l a = ∑ j : Fin n, l (EuclideanSpace.single j 1) * a j := by
  have h := congrArg l ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr a)
  simp only [map_sum, map_smul, EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply, smul_eq_mul] at h
  simpa only [mul_comm] using h.symm

/-- The full coordinate commutator, with the Hessian contraction written as a sum. -/
theorem hsGradient_commutator {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c)
    (f : HsTestFunction N) {x : HsEuclidean N} (hx : x ∈ hsChamber N)
    (i : Fin (N : ℕ)) :
    fderiv ℝ (fun y => inner ℝ (gradient (hsPairExpression χ) y) (gradient f.toFun y) - Δ f.toFun y)
        x (EuclideanSpace.single i 1) -
      (inner ℝ (gradient (hsPairExpression χ) x)
        (gradient (fun y => fderiv ℝ f.toFun y (EuclideanSpace.single i 1)) x) -
          Δ (fun y => fderiv ℝ f.toFun y (EuclideanSpace.single i 1)) x) =
      ∑ j : Fin (N : ℕ),
        fderiv ℝ (fderiv ℝ (hsPairExpression χ)) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) * gradient f.toFun x j := by
  rw [langevin_direction_commutator
    ((hsPairExpression_contDiffOn χ).contDiffAt ((isOpen_hsChamber N).mem_nhds hx)) f.smooth]
  exact hsCommutator_linear_coordinates _ _

/-- The same commutator on the anchored simplex, with all `N-1` coordinates. -/
theorem anchoredGradient_commutator {n : ℕ} {c : ℝ}
    (χ : HsPairPotentials n.succPNat c) (f : anchoredTestSubmodule n)
    {x : AnchoredEuclidean n} (hx : x ∈ anchoredSimplex n) (i : Fin n) :
    fderiv ℝ (anchoredLangevinExpr χ f) x (EuclideanSpace.single i 1) -
      anchoredLangevinExpr χ
        (fun y => fderiv ℝ (f : AnchoredEuclidean n → ℝ) y (EuclideanSpace.single i 1)) x =
      ∑ j : Fin n, fderiv ℝ (fderiv ℝ (hsAnchoredHamiltonianE χ)) x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) *
          gradient (f : AnchoredEuclidean n → ℝ) x j := by
  unfold anchoredLangevinExpr
  rw [langevin_direction_commutator
    ((contDiffOn_hsAnchoredHamiltonianE χ).contDiffAt ((isOpen_anchoredSimplex n).mem_nhds hx))
    f.property.1]
  exact hsCommutator_linear_coordinates _ _

end Riesz1
