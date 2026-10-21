/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.RieszAdmissibleBounds
public import Riesz1.HelfferSjostrand.RieszAdmissibleScalar

/-!
# Admissibility of Riesz Hamiltonians

All constants are allowed to depend on the
particle number and on the fixed potential data.
-/

@[expose] public section

noncomputable section

open Set Finset
open scoped Topology

namespace Riesz1

namespace Internal

theorem hs_admissible_of_pair_bounds (n : ℕ) {c s b B D : ℝ}
    (χ : HsPairPotentials (n + 1).succPNat c) (hc : 0 < c) (hs : 0 < s)
    (hb : 0 < b) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hforce : ∀ i j : Fin (n + 2), i < j → ∀ r a : ℝ,
      r ∈ Ioo (0 : ℝ) 1 → ((n + 1).succPNat : ℝ)⁻¹ ≤ a →
      a ≤ 1 - ((n + 1).succPNat : ℝ)⁻¹ →
      b * (r ^ (-s - 1) + (1 - r) ^ (-s - 1)) - B ≤
        deriv (χ.potential i j) r * (r - a))
    (hcurv : ∀ i j : Fin (n + 2), i < j → ∀ r δ : ℝ,
      r ∈ Ioo (0 : ℝ) 1 → 0 < δ → δ ≤ r → δ ≤ 1 - r →
      deriv (deriv (χ.potential i j)) r ≤ D * δ ^ (-s - 2)) :
    ∃ C : ℝ, HsAdmissible χ C := by
  let N := (n + 1).succPNat
  have hN : 0 < (N : ℝ) := by exact_mod_cast N.pos
  have hN₂ : 2 ≤ (N : ℕ) := by change 2 ≤ n + 1 + 1; omega
  obtain ⟨B₀, hB₀, hgrad⟩ := hs_pair_gradient_gap_lower n χ hb hB hforce
  let D₀ : ℝ := 4 * ∑ i : Fin (N : ℕ), ∑ j ∈ univ.filter (i < ·), D
  have hD₀ : 0 ≤ D₀ := mul_nonneg (by norm_num)
    (sum_nonneg (fun i _ => sum_nonneg (fun j _ => hD)))
  obtain ⟨C, hC, hbound⟩ := hs_boundary_scalar_criterion hs (div_pos hb hN)
    (div_nonneg hB₀ hN.le) hD₀ hN
  refine ⟨C, hN₂, hc, hC, ?_⟩
  intro x hx
  let δ := hsBoundaryDistance N hN₂ x * Real.sqrt 2
  have hδ : 0 < δ := mul_pos (hsBoundaryDistance_pos hN₂ hx)
    (Real.sqrt_pos.mpr (by norm_num))
  obtain ⟨i, j, hij, _⟩ := hsBoundaryDistance_pair_attains n hx
  have hpair := hsBoundaryDistance_pair_lower n hx hij
  have hδ1 : δ ≤ 1 := hpair.1.trans (hsChamber_separation_mem hx hij).2.le
  have hG : b / (N : ℝ) * δ ^ (-s - 1) - B₀ / (N : ℝ) ≤
      ‖gradient (hsPairExpression χ) x‖ := by
    have hh := hgrad x hx
    have he : b / (N : ℝ) * δ ^ (-s - 1) - B₀ / (N : ℝ) =
        (b * δ ^ (-s - 1) - B₀) / (N : ℝ) := by ring
    rw [he]
    apply (div_le_iff₀ hN).mpr
    change b * δ ^ (-s - 1) - B₀ ≤ (N : ℝ) *
      ‖gradient (hsPairExpression χ) x‖ at hh
    nlinarith
  have hL : Laplacian.laplacian (hsPairExpression χ) x ≤ D₀ * δ ^ (-s - 2) := by
    rw [laplacian_hsPairExpression χ hx]
    have hh : (∑ i : Fin (N : ℕ), ∑ j ∈ univ.filter (i < ·),
        deriv (deriv (χ.potential i j)) (x j - x i)) ≤
        ∑ i : Fin (N : ℕ), ∑ j ∈ univ.filter (i < ·), D * δ ^ (-s - 2) := by
      apply sum_le_sum
      intro i _
      apply sum_le_sum
      intro j hj
      have hij := (mem_filter.mp hj).2
      have hp := hsBoundaryDistance_pair_lower n hx hij
      exact hcurv i j hij _ δ (hsChamber_separation_mem hx hij) hδ hp.1 hp.2
    have hh' := mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 4)
    calc 4 * (∑ i, ∑ j ∈ univ.filter (i < ·),
        deriv (deriv (χ.potential i j)) (x j - x i)) ≤
        4 * (∑ i, ∑ j ∈ univ.filter (i < ·), D * δ ^ (-s - 2)) := hh'
      _ = D₀ * δ ^ (-s - 2) := by
        dsimp only [D₀]
        simp only [← sum_mul, mul_assoc]
  have hd : (hsBoundaryDistance N hN₂ x)⁻¹ ^ 2 = 2 * δ⁻¹ ^ 2 := by
    dsimp only [δ]
    have hsqrt : ((Real.sqrt (2 : ℝ))⁻¹) ^ 2 = (2 : ℝ)⁻¹ := by
      rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    rw [mul_inv_rev, mul_pow, hsqrt]
    ring
  rw [hd]
  exact hbound δ _ _ hδ hδ1 (norm_nonneg _) hG hL

end Internal

/-- The Riesz pair potentials are admissible for every `N ≥ 2`. -/
theorem hsRiesz_admissible (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (β : ℝ) (hβ : 0 < β)
    (s : RieszExponent) : ∃ C : ℝ, HsAdmissible (hsRieszPairPotentials N β hβ s) C := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hN
  have hN' : N = (n + 1).succPNat := by apply Subtype.ext; change (N : ℕ) = n + 1 + 1; omega
  subst N
  let A := β * (((n + 1).succPNat : ℕ+) : ℝ) ^ (-s.val)
  have hA : 0 < A := hsRiesz_pair_coefficient_pos _ hβ s
  have hη : 0 < (((n + 1).succPNat : ℕ+) : ℝ)⁻¹ := by positivity
  obtain ⟨b, B, hb, hB, hforce⟩ := hurwitzKernel_force_coercive s.val s.2.1 s.2.2 hη
  obtain ⟨D, hD, hcurv⟩ := hurwitzKernel_deriv2_gap_bound s.val s.2.1 s.2.2
  apply Internal.hs_admissible_of_pair_bounds n _ (hsRieszPairPotentials_curvature_pos _ hβ s)
    s.2.1 (mul_pos hA hb) (mul_nonneg hA.le hB) (mul_nonneg hA.le hD.le)
  · intro i j hij r a hr ha₀ ha₁
    have hh := mul_le_mul_of_nonneg_left (hforce a r ha₀ ha₁ hr) hA.le
    change A * b * _ - A * B ≤ deriv (fun r => A * hurwitzKernel s.val r) r * (r - a)
    rw [deriv_const_mul_field]
    nlinarith
  · intro i j hij r δ hr hδ hδr hδr'
    change deriv (deriv (fun r => A * hurwitzKernel s.val r)) r ≤ A * D * _
    rw [deriv_const_mul_field', deriv_const_mul_field]
    exact (mul_le_mul_of_nonneg_left (hcurv r δ hr hδ hδr hδr') hA.le).trans_eq (by ring)

end Riesz1

end
