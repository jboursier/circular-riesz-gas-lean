/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.GroundStatePotential
public import Riesz1.HelfferSjostrand.SobolevPeriodization
public import Riesz1.ToMathlib.Chamber.PeriodizationDerivative

/-!
# The ground-state potential on the cylinder

The potential descends through the actual
period lattice. No representative choice changes its value.
-/

@[expose] public section

noncomputable section

open Set

namespace Riesz1

variable {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c)

/-- Translation by an integer period preserves the ground-state potential. -/
theorem hsGroundStatePotential_translate (k : ℤ) (x : HsEuclidean N) :
    hsGroundStatePotential χ (hsTranslate (k : ℝ) x) = hsGroundStatePotential χ x := by
  let v := hsRotationVector N
  have hp : ∀ (j : ℤ) y, hsPairExpression χ (y + (j : ℝ) • v) = hsPairExpression χ y := by
    intro j y
    rw [← hsTranslate_eq_add_rotation]
    exact hsPairExpression_translate χ _ _
  have hd (y : HsEuclidean N) :
      fderiv ℝ (hsPairExpression χ) (y + (k : ℝ) • v) =
        fderiv ℝ (hsPairExpression χ) y := fderiv_periodic_vector hp k y
  have hdd : fderiv ℝ (fderiv ℝ (hsPairExpression χ)) (x + (k : ℝ) • v) =
      fderiv ℝ (fderiv ℝ (hsPairExpression χ)) x := by
    rw [← fderiv_comp_add_right ((k : ℝ) • v)]
    congr 1
    funext y
    exact hd y
  rw [hsGroundStatePotential, hsGroundStatePotential, hsTranslate_eq_add_rotation]
  have hg : gradient (hsPairExpression χ) (x + (k : ℝ) • v) =
      gradient (hsPairExpression χ) x := congrArg (InnerProductSpace.toDual ℝ (HsEuclidean N)).symm (hd x)
  rw [hg, laplacian_eq_sum_fderiv_fderiv _ (EuclideanSpace.basisFun _ ℝ),
    laplacian_eq_sum_fderiv_fderiv _ (EuclideanSpace.basisFun _ ℝ), hdd]

/-- The existing potential descended to the whole cylinder by periodicity. -/
def hsGroundStateCylinderPotential : HsCylinder N → ℝ :=
  Quotient.lift (hsGroundStatePotential χ) (by
    intro x y hxy
    obtain ⟨k, hk⟩ := (hsPeriodLattice_mem_iff _).mp
      (QuotientAddGroup.leftRel_apply.mp hxy)
    have he : y = hsTranslate (k : ℝ) x := by
      ext i
      have hi := hk i
      change -x i + y i = (k : ℝ) at hi
      change y i = x i + (k : ℝ)
      linarith
    rw [he, hsGroundStatePotential_translate])

/-- Descending and then lifting recovers the original formula everywhere. -/
theorem hsGroundStateCylinderPotential_mk (x : HsEuclidean N) :
    hsGroundStateCylinderPotential χ (QuotientAddGroup.mk x) = hsGroundStatePotential χ x := rfl

end Riesz1
