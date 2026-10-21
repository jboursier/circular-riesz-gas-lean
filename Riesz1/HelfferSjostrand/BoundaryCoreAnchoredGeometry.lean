/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.VectorEnergyAnchoredForm
public import Riesz1.HelfferSjostrand.GroundStatePotential
public import Riesz1.HelfferSjostrand.AnchoredCalculus
public import Riesz1.HelfferSjostrand.AnchoredInverseSpace

/-!
# Anchoring comparisons for the scalar boundary core

The gradient, Laplacian and collision-distance comparisons in the
anchored setting.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter Metric
open scoped ContDiff Laplacian

namespace Riesz1

variable {n : ℕ} {c : ℝ}

/-- Membership in the anchored simplex is exactly membership of the lift
in the cyclic chamber. -/
theorem boundaryCore_anchorLift_mem_chamber_iff (y : AnchoredEuclidean n) :
    anchorLift n y ∈ hsChamber n.succPNat ↔ y ∈ anchoredSimplex n := by
  constructor
  · intro hy
    refine ⟨fun i => ⟨?_, ?_⟩, fun i j hij => ?_⟩
    · exact hy.1 (Fin.succ_pos i)
    · have h := hy.2 i.succ
      simpa [anchorLift_apply, anchorVector] using h
    · exact hy.1 (Fin.succ_lt_succ_iff.mpr hij)
  · exact anchorLift_mem_chamber

/-- Coordinate vectors in the anchored space lift to the corresponding
tail coordinate vectors in the particle space. -/
theorem boundaryCore_anchorLift_single (i : Fin n) :
    anchorLift n (EuclideanSpace.single i (1 : ℝ)) = EuclideanSpace.single i.succ 1 := by
  ext j
  induction j using Fin.cases with
  | zero => simp [anchorLift_apply, anchorVector]
  | succ j => simp [anchorLift_apply, anchorVector, PiLp.single_apply, Pi.single_apply]

private theorem gradient_coord_eq_fderiv_single {m : ℕ}
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (x : EuclideanSpace ℝ (Fin m)) (i : Fin m) :
    fderiv ℝ f x (EuclideanSpace.single i 1) = gradient f x i := by
  rw [← inner_gradient_left]
  simp only [EuclideanSpace.inner_single_right, starRingEnd_apply, star_trivial, one_mul]

/-- The anchored gradient consists of the tail coordinates of the
ambient gradient at the anchored lift. -/
theorem boundaryCore_anchored_gradient_coord (χ : HsPairPotentials n.succPNat c)
    {y : AnchoredEuclidean n} (hy : y ∈ anchoredSimplex n) (i : Fin n) :
    gradient (hsAnchoredHamiltonianE χ) y i =
      gradient (hsPairExpression χ) (anchorLift n y) i.succ := by
  have hd := ((hasFDerivAt_hsPairExpression χ (anchorLift_mem_chamber hy)).comp y
    (anchorLift n).hasFDerivAt).fderiv
  have he : fderiv ℝ (hsAnchoredHamiltonianE χ) y =
      (fderiv ℝ (hsPairExpression χ) (anchorLift n y)).comp (anchorLift n) := by
    rw [(hasFDerivAt_hsPairExpression χ (anchorLift_mem_chamber hy)).fderiv]
    exact hd
  have h := congrArg (fun A : AnchoredEuclidean n →L[ℝ] ℝ => A (EuclideanSpace.single i 1)) he
  simp only [ContinuousLinearMap.comp_apply, boundaryCore_anchorLift_single] at h
  exact (gradient_coord_eq_fderiv_single (hsAnchoredHamiltonianE χ) y i).symm.trans
    (h.trans (gradient_coord_eq_fderiv_single (m := (n.succPNat : ℕ))
      (hsPairExpression χ) (anchorLift n y) i.succ))

/-- The ambient gradient has zero coordinate sum, from common-translation
invariance of the Hamiltonian. -/
theorem boundaryCore_gradient_sum {N : ℕ+} (χ : HsPairPotentials N c)
    {x : HsEuclidean N} (hx : x ∈ hsChamber N) :
    ∑ i, gradient (hsPairExpression χ) x i = 0 := by
  have hz : fderiv ℝ (hsPairExpression χ) x (hsRotationVector N) = 0 := by
    rw [(hasFDerivAt_hsPairExpression χ hx).fderiv]
    simp [hsPairGradient, hsSeparation, hsRotationVector]
  rw [← inner_gradient_left] at hz
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, hsRotationVector,
    WithLp.ofLp_toLp, Pi.star_apply, star_trivial, one_mul] using hz

/-- The factor `N` in the anchored gradient comparison. -/
theorem boundaryCore_anchored_gradient_norm (χ : HsPairPotentials n.succPNat c)
    {y : AnchoredEuclidean n} (hy : y ∈ anchoredSimplex n) :
    ‖gradient (hsPairExpression χ) (anchorLift n y)‖ ^ 2 ≤
      (n + 1 : ℝ) * ‖gradient (hsAnchoredHamiltonianE χ) y‖ ^ 2 := by
  let a := gradient (hsAnchoredHamiltonianE χ) y
  let g : EuclideanSpace ℝ (Fin (n + 1)) := gradient (hsPairExpression χ) (anchorLift n y)
  have hg (i : Fin n) : g i.succ = a i := (boundaryCore_anchored_gradient_coord χ hy i).symm
  have hzero := boundaryCore_gradient_sum χ (anchorLift_mem_chamber hy)
  change (∑ i : Fin (n + 1), g i) = 0 at hzero
  rw [Fin.sum_univ_succ] at hzero
  simp only [hg] at hzero
  have hsq := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin n => (1 : ℝ)) (fun i => a i)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one] at hsq
  have hnorm : ‖g‖ ^ 2 = (g 0) ^ 2 + ∑ i, (a i) ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
    change (∑ i : Fin (n + 1), (g i) ^ 2) = _
    rw [Fin.sum_univ_succ]
    simp only [hg]
  have hanorm : ‖a‖ ^ 2 = ∑ i, (a i) ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
  change ‖g‖ ^ 2 ≤ _ * ‖a‖ ^ 2
  rw [hnorm, hanorm]
  have h0 : g 0 = -(∑ i, a i) := by linarith
  rw [h0, neg_sq]
  nlinarith

/-- The anchored Laplacian omits a nonnegative ambient Hessian diagonal. -/
theorem boundaryCore_anchored_laplacian_le (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    {y : AnchoredEuclidean n} (hy : y ∈ anchoredSimplex n) :
    Δ (hsAnchoredHamiltonianE χ) y ≤ Δ (hsPairExpression χ) (anchorLift n y) := by
  have he : Δ (hsAnchoredHamiltonianE χ) y =
      ∑ i : Fin n, fderiv ℝ (fderiv ℝ (hsAnchoredHamiltonianE χ)) y
        (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
    simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
      (EuclideanSpace.basisFun _ ℝ), iteratedFDeriv_two_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, EuclideanSpace.basisFun_apply]
  let F : Fin (n + 1) → ℝ := fun i => fderiv ℝ (fderiv ℝ (hsPairExpression χ))
    (anchorLift n y) (EuclideanSpace.single (ι := Fin (n.succPNat : ℕ)) i 1)
      (EuclideanSpace.single (ι := Fin (n.succPNat : ℕ)) i 1)
  have hamb : Δ (hsPairExpression χ) (anchorLift n y) = ∑ i : Fin (n + 1), F i := by
    have ht := laplacian_eq_sum_fderiv_fderiv (hsPairExpression χ)
      (EuclideanSpace.basisFun (Fin (n.succPNat : ℕ)) ℝ) (anchorLift n y)
    simp only [EuclideanSpace.basisFun_apply] at ht
    convert ht using 1
    rfl
  have htail : Δ (hsAnchoredHamiltonianE χ) y = ∑ i : Fin n, F i.succ := by
    rw [he]
    apply Finset.sum_congr rfl
    intro i _
    rw [fderiv_fderiv_hsAnchoredHamiltonianE χ (anchorLift_mem_chamber hy),
      boundaryCore_anchorLift_single]
    rfl
  rw [htail, hamb, Fin.sum_univ_succ]
  exact le_add_of_nonneg_left (hsPairExpression_hessian_nonnegative χ hc
    (anchorLift_mem_chamber hy) _)

/-- Anchoring increases distance to the collision complement, since the
anchored lift is isometric and maps the anchored complement into the
ambient collision complement. -/
theorem boundaryCore_anchored_distance (hn : 0 < n) (hN : 2 ≤ (n.succPNat : ℕ))
    (y : AnchoredEuclidean n) :
    hsBoundaryDistance n.succPNat hN (anchorLift n y) ≤ infDist y (anchoredSimplex n)ᶜ := by
  have hne : (anchoredSimplex n)ᶜ.Nonempty := by
    refine ⟨0, fun h => ?_⟩
    have hi := (h.1 ⟨0, hn⟩).1
    exact (lt_irrefl (0 : ℝ)) hi
  apply (le_infDist hne).mpr
  intro z hz
  have hzc : anchorLift n z ∈ (hsChamber n.succPNat)ᶜ :=
    fun h => hz ((boundaryCore_anchorLift_mem_chamber_iff z).mp h)
  calc
    _ ≤ dist (anchorLift n y) (anchorLift n z) := infDist_le_dist_of_mem hzc
    _ = dist y z := by rw [dist_eq_norm, ← map_sub, norm_anchorLift, dist_eq_norm]

/-- The ground-state potential of the anchored Hamiltonian. -/
def hsAnchoredGroundStatePotential (χ : HsPairPotentials n.succPNat c)
    (y : AnchoredEuclidean n) : ℝ :=
  ‖gradient (hsAnchoredHamiltonianE χ) y‖ ^ 2 / 4 - Δ (hsAnchoredHamiltonianE χ) y / 2

/-- The admissibility assumption implies the anchored inverse-square
barrier with exactly the same constant. -/
theorem hsAnchoredGroundStatePotential_boundary_lower (χ : HsPairPotentials n.succPNat c)
    (hc : 0 < c) {C_N : ℝ} (hadm : HsAdmissible χ C_N)
    {y : AnchoredEuclidean n} (hy : y ∈ anchoredSimplex n) :
    (infDist y (anchoredSimplex n)ᶜ)⁻¹ ^ 2 - C_N ≤ hsAnchoredGroundStatePotential χ y := by
  have hn : 0 < n := by have hN := hadm.choose; change 2 ≤ n + 1 at hN; omega
  have hx := anchorLift_mem_chamber hy
  have hd := boundaryCore_anchored_distance hn hadm.choose y
  have hp := hsBoundaryDistance_pos hadm.choose hx
  have hi := (inv_le_inv₀ (hp.trans_le hd) hp).mpr hd
  have hisq : (infDist y (anchoredSimplex n)ᶜ)⁻¹ ^ 2 ≤
      (hsBoundaryDistance n.succPNat hadm.choose (anchorLift n y))⁻¹ ^ 2 :=
    pow_le_pow_left₀ (inv_nonneg.mpr (hp.trans_le hd).le) hi 2
  have hg := boundaryCore_anchored_gradient_norm χ hy
  have hl := boundaryCore_anchored_laplacian_le χ hc hy
  have hb := hadm.choose_spec.2.2 _ hx
  have hNpos : 0 < (n + 1 : ℝ) := by positivity
  have hgrad : ‖gradient (hsPairExpression χ) (anchorLift n y)‖ ^ 2 / (4 * (n + 1 : ℝ)) ≤
      ‖gradient (hsAnchoredHamiltonianE χ) y‖ ^ 2 / 4 := by
    apply (div_le_div_iff₀ (mul_pos (by norm_num) hNpos) (by norm_num)).mpr
    nlinarith [hg]
  change _ ≤ ‖gradient (hsAnchoredHamiltonianE χ) y‖ ^ 2 / 4 -
    Δ (hsAnchoredHamiltonianE χ) y / 2
  simp only [Nat.succPNat_coe, Nat.cast_succ] at hb
  calc
    _ ≤ (hsBoundaryDistance n.succPNat hadm.choose (anchorLift n y))⁻¹ ^ 2 - C_N :=
      sub_le_sub_right hisq C_N
    _ ≤ _ := hb
    _ ≤ _ := sub_le_sub hgrad (div_le_div_of_nonneg_right hl (by norm_num))

end Riesz1
