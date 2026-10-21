/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.RieszAdmissiblePairs
public import Riesz1.HelfferSjostrand.RieszAdmissibleGeometry
public import Riesz1.HelfferSjostrand.GeometryRelabelAdmissible

/-!
# Differential bounds for Riesz admissibility

The gradient lower bound and Laplacian upper bound for Riesz admissibility.
Conditional estimates are internal lemmas. They are not admissibility
statements.
-/

@[expose] public section

noncomputable section

open Set Finset
open scoped Topology

namespace Riesz1

/-- The Laplacian is four times the sum of the pair curvatures. -/
theorem laplacian_hsPairExpression {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c)
    {x : HsEuclidean N} (hx : x ∈ hsChamber N) :
    Laplacian.laplacian (hsPairExpression χ) x =
      4 * ∑ i : Fin (N : ℕ), ∑ j ∈ univ.filter (i < ·),
        deriv (deriv (χ.potential i j)) (x j - x i) := by
  rw [laplacian_eq_sum_fderiv_fderiv _ (EuclideanSpace.basisFun _ ℝ)]
  simp_rw [hessian_hsPairExpression_self χ hx, EuclideanSpace.basisFun_apply]
  rw [← mul_sum, sum_comm]
  simp_rw [sum_comm (s := univ) (t := univ.filter _)]
  have hnorm (i j : Fin (N : ℕ)) (hij : i < j) :
      (∑ k : Fin (N : ℕ),
        ((EuclideanSpace.single k (1 : ℝ)) j - (EuclideanSpace.single k (1 : ℝ)) i) ^ 2) = 2 := by
    have he (k : Fin (N : ℕ)) :
        ((EuclideanSpace.single k (1 : ℝ)) j - (EuclideanSpace.single k (1 : ℝ)) i) ^ 2 =
          (if k = i then 1 else 0) + (if k = j then 1 else 0) := by
      by_cases hki : k = i
      · subst k
        simp [hij.ne, hij.ne']
      · by_cases hkj : k = j
        · subst k
          simp [hij.ne, hij.ne']
        · simp [hki, hkj]
    simp_rw [he, sum_add_distrib]
    norm_num
  simp_rw [← mul_sum]
  rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_assoc]
  congr 1
  rw [mul_sum]
  apply sum_congr rfl
  intro i _
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  rw [hnorm i j (mem_filter.mp hj).2]
  ring

namespace Internal

/-- The comparison displacement tests the gradient against the sum of the pair forces. -/
theorem hs_pair_force_identity {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c)
    {x : HsEuclidean N} (hx : x ∈ hsChamber N) :
    fderiv ℝ (hsPairExpression χ) x (x - hsEquispacedComparison x) =
      2 * ∑ i : Fin (N : ℕ), ∑ j ∈ univ.filter (i < ·),
        deriv (χ.potential i j) (x j - x i) *
          (x j - x i - (hsEquispacedComparison x j - hsEquispacedComparison x i)) := by
  rw [(hasFDerivAt_hsPairExpression χ hx).fderiv]
  unfold hsPairGradient
  simp only [smul_apply, _root_.sum_apply,
    smul_eq_mul, hsSeparation_apply, PiLp.sub_apply]
  congr 1
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  ring

theorem hs_pair_gradient_gap_lower (n : ℕ) {c s b B : ℝ}
    (χ : HsPairPotentials (n + 1).succPNat c) (hb : 0 < b) (hB : 0 ≤ B)
    (hforce : ∀ i j : Fin (n + 2), i < j → ∀ r a : ℝ,
      r ∈ Ioo (0 : ℝ) 1 → ((n + 1).succPNat : ℝ)⁻¹ ≤ a →
      a ≤ 1 - ((n + 1).succPNat : ℝ)⁻¹ →
      b * (r ^ (-s - 1) + (1 - r) ^ (-s - 1)) - B ≤
        deriv (χ.potential i j) r * (r - a)) :
    ∃ B₀ : ℝ, 0 ≤ B₀ ∧ ∀ x ∈ hsChamber (n + 1).succPNat,
      b * (hsBoundaryDistance (n + 1).succPNat
        (by change 2 ≤ n + 1 + 1; omega) x * Real.sqrt 2) ^ (-s - 1) - B₀ ≤
        ((n + 1).succPNat : ℝ) * ‖gradient (hsPairExpression χ) x‖ := by
  let B₀ : ℝ := ∑ i : Fin (n + 2), ∑ j ∈ univ.filter (i < ·), B
  refine ⟨B₀, sum_nonneg (fun i _ => sum_nonneg (fun j _ => hB)), ?_⟩
  intro x hx
  let δ := hsBoundaryDistance (n + 1).succPNat
    (by change 2 ≤ n + 1 + 1; omega) x * Real.sqrt 2
  let F (i j : Fin (n + 2)) := deriv (χ.potential i j) (x j - x i) *
    (x j - x i - (hsEquispacedComparison x j - hsEquispacedComparison x i))
  have hF (i j : Fin (n + 2)) (hij : i < j) :
      b * ((x j - x i) ^ (-s - 1) + (1 - (x j - x i)) ^ (-s - 1)) ≤ F i j + B := by
    have ha := hsEquispacedComparison_separation_bounds x hij
    have hh := hforce i j hij _ _ (hsChamber_separation_mem hx hij) ha.1 ha.2
    dsimp only [F]
    linarith
  have hF₀ (i j : Fin (n + 2)) (hij : i < j) : 0 ≤ F i j + B := by
    apply le_trans _ (hF i j hij)
    have hr := hsChamber_separation_mem hx hij
    exact mul_nonneg hb.le (add_nonneg (Real.rpow_nonneg hr.1.le _)
      (Real.rpow_nonneg (by linarith [hr.2]) _))
  obtain ⟨i, j, hij, hat⟩ := hsBoundaryDistance_pair_attains n hx
  have hpair : b * δ ^ (-s - 1) ≤ F i j + B := by
    have h := hF i j hij
    rcases hat with hδ | hδ
    · change x j - x i = δ at hδ
      rw [hδ] at h
      have hh : 0 ≤ (1 - δ) ^ (-s - 1) := Real.rpow_nonneg
        (by rw [← hδ]; linarith [(hsChamber_separation_mem hx hij).2]) _
      nlinarith
    · change 1 - (x j - x i) = δ at hδ
      rw [hδ] at h
      have hh : 0 ≤ (x j - x i) ^ (-s - 1) :=
        Real.rpow_nonneg (hsChamber_separation_mem hx hij).1.le _
      nlinarith
  have hsum : b * δ ^ (-s - 1) ≤
      ∑ i : Fin (n + 2), ∑ j ∈ univ.filter (i < ·), (F i j + B) := by
    apply hpair.trans
    apply (single_le_sum (fun k hk => hF₀ i k (mem_filter.mp hk).2)
      (mem_filter.mpr ⟨mem_univ _, hij⟩)).trans
    exact single_le_sum (fun k _ => sum_nonneg (fun l hl =>
      hF₀ k l (mem_filter.mp hl).2)) (mem_univ _)
  simp_rw [sum_add_distrib] at hsum
  have he := hs_pair_force_identity χ hx
  change fderiv ℝ (hsPairExpression χ) x (x - hsEquispacedComparison x) =
    2 * ∑ i : Fin (n + 2), ∑ j ∈ univ.filter (i < ·), F i j at he
  have hnorm := (fderiv ℝ (hsPairExpression χ) x).le_opNorm
    (x - hsEquispacedComparison x)
  rw [← norm_gradient_eq_norm_fderiv] at hnorm
  have hnorm' := mul_le_mul_of_nonneg_left (norm_sub_hsEquispacedComparison_le hx)
    (norm_nonneg (gradient (hsPairExpression χ) x))
  have habs := le_abs_self (fderiv ℝ (hsPairExpression χ) x (x - hsEquispacedComparison x))
  rw [Real.norm_eq_abs] at hnorm
  change b * δ ^ (-s - 1) - B₀ ≤ _
  change b * δ ^ (-s - 1) ≤
    (∑ i : Fin (n + 2), ∑ j ∈ univ.filter (i < ·), F i j) + B₀ at hsum
  -- When the sum of forces is negative, its fixed lower bound handles this case.
  by_cases hpos : 0 ≤ ∑ i : Fin (n + 2), ∑ j ∈ univ.filter (i < ·), F i j
  · nlinarith
  · have : b * δ ^ (-s - 1) - B₀ ≤ 0 := by linarith
    exact this.trans (by positivity)

end Internal

end Riesz1

end
