/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.HurwitzKernel.EndpointEstimates

/-!
# Domination of the boundary powers

The scalar last step of the Riesz admissibility bounds: the square of a force
of order `δ^(-s-1)` dominates curvature of order `δ^(-s-2)` and `δ⁻²`.
The estimates are internal conditional lemmas.
-/

public section

noncomputable section

open Set Filter
open scoped Topology

namespace Riesz1.Internal

theorem hs_boundary_power_domination {s a D : ℝ} (hs : 0 < s) (ha : 0 < a)
    (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      2 * δ⁻¹ ^ 2 ≤
        a * (δ ^ (-s - 1)) ^ 2 - D * δ ^ (-s - 2) + C := by
  have hlim := tendsto_rpow_neg_nhdsGT_zero (neg_lt_zero.mpr hs)
  have hev : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      max (2 * D / a) (Real.sqrt (4 / a)) ≤ δ ^ (-s) :=
    hlim.eventually_ge_atTop _
  obtain ⟨ε, hε, he⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  change 0 < ε at hε
  let C := D * ε ^ (-s - 2) + 2 * ε⁻¹ ^ 2
  refine ⟨C, by positivity, ?_⟩
  intro δ hδ hδ1
  by_cases hδε : δ < ε
  · have ht := he ⟨hδ, hδε⟩
    change max (2 * D / a) (Real.sqrt (4 / a)) ≤ δ ^ (-s) at ht
    have ht₀ : 0 ≤ δ ^ (-s) := Real.rpow_nonneg hδ.le _
    have h₁ : 2 * D ≤ a * δ ^ (-s) := by
      simpa only [mul_comm] using (div_le_iff₀ ha).mp ((le_max_left _ _).trans ht)
    have h₂ : 4 ≤ a * (δ ^ (-s)) ^ 2 := by
      have hsqrt := (le_max_right _ _).trans ht
      have hsqrt₂ := Real.sq_sqrt (show 0 ≤ 4 / a by positivity)
      have hh : 4 / a ≤ (δ ^ (-s)) ^ 2 := by
        nlinarith [Real.sqrt_nonneg (4 / a)]
      simpa only [mul_comm] using (div_le_iff₀ ha).mp hh
    have hpoly : 2 ≤ a * (δ ^ (-s)) ^ 2 - D * δ ^ (-s) := by
      nlinarith
    have hr₁ : δ ^ (-s - 1) = δ ^ (-s) * δ⁻¹ := by
      rw [Real.rpow_sub hδ, Real.rpow_one, div_eq_mul_inv]
    have hr₂ : δ ^ (-s - 2) = δ ^ (-s) * δ⁻¹ ^ 2 := by
      rw [Real.rpow_sub hδ, Real.rpow_two, div_eq_mul_inv, inv_pow]
    rw [hr₁, hr₂]
    have hh := mul_le_mul_of_nonneg_right hpoly (sq_nonneg δ⁻¹)
    dsimp only [C]
    nlinarith [mul_nonneg hD (Real.rpow_nonneg hε.le (-s - 2)), sq_nonneg ε⁻¹]
  · have hδε' : ε ≤ δ := le_of_not_gt hδε
    have hp := Real.rpow_le_rpow_of_nonpos hε hδε' (by linarith : -s - 2 ≤ 0)
    have hi : δ⁻¹ ≤ ε⁻¹ := inv_anti₀ hε hδε'
    have hi₀ : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδ.le
    have hsq : δ⁻¹ ^ 2 ≤ ε⁻¹ ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hp hD
    have ha₀ := mul_nonneg ha.le (sq_nonneg (δ ^ (-s - 1)))
    dsimp only [C]
    linarith

theorem hs_boundary_scalar_criterion {s b B D n : ℝ}
    (hs : 0 < s) (hb : 0 < b) (hB : 0 ≤ B) (hD : 0 ≤ D) (hn : 0 < n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ δ G L : ℝ, 0 < δ → δ ≤ 1 → 0 ≤ G →
      b * δ ^ (-s - 1) - B ≤ G → L ≤ D * δ ^ (-s - 2) →
      2 * δ⁻¹ ^ 2 - C ≤ G ^ 2 / (4 * n) - L / 2 := by
  have ha : 0 < b ^ 2 / (8 * n) := by positivity
  obtain ⟨C, hC, hpow⟩ := hs_boundary_power_domination hs ha
    (show 0 ≤ D / 2 by positivity)
  refine ⟨C + B ^ 2 / (4 * n), by positivity, ?_⟩
  intro δ G L hδ hδ1 hG hforce hL
  have hu : 0 ≤ b * δ ^ (-s - 1) := by positivity
  have hsq : b ^ 2 * (δ ^ (-s - 1)) ^ 2 ≤ 2 * G ^ 2 + 2 * B ^ 2 := by
    nlinarith [sq_nonneg (G - B)]
  have hsq' : b ^ 2 / (8 * n) * (δ ^ (-s - 1)) ^ 2 ≤
      G ^ 2 / (4 * n) + B ^ 2 / (4 * n) := by
    calc b ^ 2 / (8 * n) * (δ ^ (-s - 1)) ^ 2 =
        (b ^ 2 * (δ ^ (-s - 1)) ^ 2) / (8 * n) := by ring
      _ ≤ (2 * G ^ 2 + 2 * B ^ 2) / (8 * n) :=
        div_le_div_of_nonneg_right hsq (by positivity)
      _ = G ^ 2 / (4 * n) + B ^ 2 / (4 * n) := by ring
  have hp := hpow δ hδ hδ1
  linarith

end Riesz1.Internal

end
