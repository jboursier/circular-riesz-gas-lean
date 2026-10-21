/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.GeometryLawCoordinates

/-!
# The radial domain `B_N` is open, convex and bounded

The radial domain `B_N = {z ∈ e^⊥ : z ∈ 𝒞_N}` is the chamber inside the
hyperplane `e^⊥`. Its openness and convexity come from the chamber, which is an intersection of
strict linear inequalities. Boundedness uses the zero-sum condition that `e^⊥` imposes.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

namespace Riesz1

variable {N : ℕ+}

/-- A vector orthogonal to `e` has coordinate sum zero. -/
theorem sum_coord_eq_zero_of_mem_orth (z : HsEuclidean N) (hz : z ∈ hsOrthSubspace N) :
    ∑ i, z i = 0 := by
  have hinner : inner ℝ (hsUnitVector N) z = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp hz
  have h1 : inner ℝ (hsUnitVector N) z = (Real.sqrt (N : ℕ))⁻¹ * ∑ i, z i := by
    simp [hsUnitVector, hsRotationVector, PiLp.inner_apply, inner_smul_left, Finset.mul_sum]
  rw [h1] at hinner
  have hsqrt : Real.sqrt (N : ℕ) ≠ 0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr N.pos)).ne'
  rcases mul_eq_zero.mp hinner with h | h
  · exact absurd (inv_eq_zero.mp h) hsqrt
  · exact h

/-- The radial domain is open in `e^⊥`: it is the preimage of the open chamber. -/
theorem isOpen_hsRadialDomain (N : ℕ+) : IsOpen (hsRadialDomain N) :=
  (isOpen_hsChamber N).preimage continuous_subtype_val

/-- The radial domain is convex in `e^⊥`: convexity of the chamber, since `e^⊥` is a subspace. -/
theorem convex_hsRadialDomain (N : ℕ+) : Convex ℝ (hsRadialDomain N) := by
  intro z hz w hw a b ha hb hab
  show ((a • z + b • w : hsOrthSubspace N) : HsEuclidean N) ∈ hsChamber N
  rw [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul]
  exact convex_hsChamber N hz hw ha hb hab

/-- Every coordinate of a point of the radial domain lies in `(-1, 1)`. The zero-sum condition
forces the first coordinate into `(-1, 0]`, and every other coordinate lies within one unit of it.
-/
theorem abs_coord_lt_one_of_mem_radialDomain {z : hsOrthSubspace N}
    (hz : z ∈ hsRadialDomain N) (i : Fin (N : ℕ)) : |(z : HsEuclidean N) i| < 1 := by
  set x : HsEuclidean N := (z : HsEuclidean N) with hxdef
  have hchamber : x ∈ hsChamber N := hz
  have hsum : ∑ j, x j = 0 := sum_coord_eq_zero_of_mem_orth x z.2
  set x0 := x ⟨0, N.pos⟩ with hx0
  have hlow : ∀ j, x0 ≤ x j := fun j =>
    hchamber.1.monotone (Fin.le_def.mpr (Nat.zero_le _))
  have hup : ∀ j, x j < x0 + 1 := fun j => hchamber.2 j
  have hrel : ∑ j, (x j - x0) = -((N : ℕ) : ℝ) * x0 := by
    simp only [Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  have hnonneg : 0 ≤ ∑ j, (x j - x0) :=
    Finset.sum_nonneg fun j _ => sub_nonneg.mpr (hlow j)
  have hlt : ∑ j, (x j - x0) < ((N : ℕ) : ℝ) := by
    have hcard : ∑ _j : Fin (N : ℕ), (1 : ℝ) = ((N : ℕ) : ℝ) := by simp
    rw [← hcard]
    exact Finset.sum_lt_sum_of_nonempty ⟨⟨0, N.pos⟩, Finset.mem_univ _⟩
      fun j _ => by linarith [hup j]
  have hN : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
  have hx0le : x0 ≤ 0 := by
    have h := hnonneg
    rw [hrel] at h
    nlinarith
  have hx0gt : -1 < x0 := by
    have h := hlt
    rw [hrel] at h
    nlinarith
  have hi1 := hlow i
  have hi2 := hup i
  rw [abs_lt]
  constructor <;> linarith

/-- The radial domain is bounded: its coordinates lie in `(-1, 1)`, so its Euclidean norm is at
most `N`. -/
theorem isBounded_hsRadialDomain (N : ℕ+) : Bornology.IsBounded (hsRadialDomain N) := by
  refine isBounded_iff_forall_norm_le.mpr ⟨((N : ℕ) : ℝ), fun z hz => ?_⟩
  show ‖(z : HsEuclidean N)‖ ≤ ((N : ℕ) : ℝ)
  rw [EuclideanSpace.norm_eq]
  have hN : (0 : ℝ) ≤ ((N : ℕ) : ℝ) := Nat.cast_nonneg _
  refine Real.sqrt_le_iff.mpr ⟨hN, ?_⟩
  have hsq : ∀ i : Fin (N : ℕ), ‖(z : HsEuclidean N) i‖ ^ 2 ≤ 1 := fun i => by
    have h := abs_coord_lt_one_of_mem_radialDomain hz i
    rw [Real.norm_eq_abs]
    nlinarith [abs_nonneg ((z : HsEuclidean N) i)]
  have hcard : ∑ _i : Fin (N : ℕ), (1 : ℝ) = ((N : ℕ) : ℝ) := by simp
  have hle : ∑ i : Fin (N : ℕ), ‖(z : HsEuclidean N) i‖ ^ 2 ≤ ((N : ℕ) : ℝ) := by
    rw [← hcard]
    exact Finset.sum_le_sum fun i _ => hsq i
  have hN1 : ((N : ℕ) : ℝ) ≤ ((N : ℕ) : ℝ) ^ 2 := by
    have h1 : (1 : ℝ) ≤ ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
    nlinarith
  exact hle.trans hN1

end Riesz1

end
end
