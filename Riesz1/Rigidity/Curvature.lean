/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.CurvaturePair
public import Riesz1.HelfferSjostrand.GeometryHessian

/-!
# The internal convexified block energy and its uniform Hessian bound

The ambient formula is used only on the open lifted block chamber. The
number `N` in the microscopic scaling is the full system size, whereas
`M` is the retained block size. Thus `M = L + 1`.
-/

@[expose] public section

noncomputable section

open Set Filter Finset
open scoped Topology ContDiff

namespace Riesz1

/-- The internal energy `H_I` in consecutive block lifts. -/
def internalConvexifiedEnergy (N M : ℕ+) (s : RieszExponent)
    (θ : ℝ → ℝ) (R : ℝ) (z : HsEuclidean M) : ℝ :=
  2 * ∑ i : Fin (M : ℕ), ∑ j ∈ univ.filter (i < ·),
    curvaturePairPotential N s θ R (z j - z i)

/-- The formula of `H_I`, using the Riesz representative. -/
theorem internalConvexifiedEnergy_eq (N M : ℕ+) (s : RieszExponent)
    (θ : ℝ → ℝ) (R : ℝ) (z : HsEuclidean M) :
    internalConvexifiedEnergy N M s θ R z =
      2 * ∑ i : Fin (M : ℕ), ∑ j ∈ univ.filter (i < ·),
        ((N : ℝ) ^ (-s.val) * rieszRepresentative s (z j - z i) +
          θ ((N : ℝ) * (z j - z i) / R)) := by
  unfold internalConvexifiedEnergy curvaturePairPotential
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  ring

/-- The internal block pairs as data in the Helffer--Sjostrand setting.
The pair curvature is half the coefficient in the full energy Hessian. -/
def curvaturePairPotentials (N M : ℕ+) (s : RieszExponent)
    {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) {R : ℝ} (hR : 1 ≤ R) :
    HsPairPotentials M
      (rigidityCurvatureConstant s.val * (N : ℝ) ^ 2 * R ^ (-s.val - 2) / 2) where
  potential := fun _ _ => curvaturePairPotential N s θ R
  symmetric := fun _ _ => rfl
  smooth := fun _ _ _ => curvaturePairPotential_smooth N s hθ R
  curvature := by
    intro i j hij r hr
    linarith [curvaturePairPotential_lower N s hθ hR hr]
  leftBoundary := by
    intro i j hij
    have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
    have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
    apply tendsto_atTop_mono' (𝓝[>] (0 : ℝ)) _
      ((tendsto_hurwitzKernel_left s.val s.2.1 s.2.2).const_mul_atTop
        (Real.rpow_pos_of_pos hN (-s.val)))
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact le_add_of_nonneg_right (hθ.2.2.1 _
      (mul_nonneg (div_nonneg hN.le hR0.le) hr.le))
  rightBoundary := by
    intro i j hij
    have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
    have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
    apply tendsto_atTop_mono' (𝓝[<] (1 : ℝ)) _
      ((tendsto_hurwitzKernel_right s.val s.2.1 s.2.2).const_mul_atTop
        (Real.rpow_pos_of_pos hN (-s.val)))
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with r hr
    exact le_add_of_nonneg_right (hθ.2.2.1 _
      (mul_nonneg (div_nonneg hN.le hR0.le) hr.le))

theorem internalConvexifiedEnergy_eq_pairExpression (N M : ℕ+) (s : RieszExponent)
    {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) {R : ℝ} (hR : 1 ≤ R) :
    internalConvexifiedEnergy N M s θ R =
      hsPairExpression (curvaturePairPotentials N M s hθ hR) := rfl

/-- Exact Hessian of `H_I`, with all pairs counted once and the factor two. -/
theorem internalConvexifiedEnergy_hessian (N M : ℕ+) (s : RieszExponent)
    {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) {R : ℝ} (hR : 1 ≤ R)
    {z : HsEuclidean M} (hz : z ∈ hsChamber M) (u : HsEuclidean M) :
    fderiv ℝ (fderiv ℝ (internalConvexifiedEnergy N M s θ R)) z u u =
      2 * ∑ i : Fin (M : ℕ), ∑ j ∈ univ.filter (i < ·),
        deriv (deriv (curvaturePairPotential N s θ R)) (z j - z i) * (u j - u i) ^ 2 :=
  hessian_hsPairExpression_self (curvaturePairPotentials N M s hθ hR) hz u

/-- Uniform Hessian lower bound for the internal energy. The same explicit
`a_s` works for every cutoff, system size, block size, and `R ≥ 1`. -/
theorem internalConvexifiedEnergy_hessian_lower (N M : ℕ+) (s : RieszExponent)
    {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ) {R : ℝ} (hR : 1 ≤ R)
    {z : HsEuclidean M} (hz : z ∈ hsChamber M) (u : HsEuclidean M) :
    rigidityCurvatureConstant s.val * (N : ℝ) ^ 2 * R ^ (-s.val - 2) *
        (∑ i : Fin (M : ℕ), ∑ j ∈ univ.filter (i < ·), (u j - u i) ^ 2) ≤
      fderiv ℝ (fderiv ℝ (internalConvexifiedEnergy N M s θ R)) z u u := by
  rw [internalConvexifiedEnergy_hessian N M s hθ hR hz u]
  simp only [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj => ?_
  have h := mul_le_mul_of_nonneg_right
    (curvaturePairPotential_lower N s hθ hR
      (hsChamber_separation_mem hz (mem_filter.mp hj).2)) (sq_nonneg (u j - u i))
  nlinarith [h]

/-- The same assertion at the actual lifted block of every configuration,
including wrapping blocks and negative starting labels. -/
theorem liftedBlock_internalConvexifiedEnergy_hessian_lower {N : ℕ+}
    (s : RieszExponent) {θ : ℝ → ℝ} (hθ : IsForcingCutoff θ)
    {R : ℝ} (hR : 1 ≤ R) (i0 : ℤ) {L : ℕ} (hL : L < (N : ℕ))
    (X : Configuration N) (u : HsEuclidean L.succPNat) :
    rigidityCurvatureConstant s.val * (N : ℝ) ^ 2 * R ^ (-s.val - 2) *
        (∑ i : Fin (L + 1), ∑ j ∈ univ.filter (i < ·), (u j - u i) ^ 2) ≤
      fderiv ℝ (fderiv ℝ (internalConvexifiedEnergy N L.succPNat s θ R))
        (WithLp.toLp 2 (liftedBlock i0 hL X).val) u u := by
  apply internalConvexifiedEnergy_hessian_lower N L.succPNat s hθ hR
  exact ⟨(liftedBlock i0 hL X).property.1, (liftedBlock i0 hL X).property.2.2.2⟩

end Riesz1

end
