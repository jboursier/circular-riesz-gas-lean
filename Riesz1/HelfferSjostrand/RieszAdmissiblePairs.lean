/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.SettingHamiltonian
public import Riesz1.Kernel.FundamentalSeries
public import Riesz1.ToMathlib.HurwitzKernel.EndpointEstimates

/-!
# Riesz pair potentials and convex pair perturbations

The pair-potential part of the admissibility of the Riesz Hamiltonian: smoothness, a uniform
positive curvature and divergence at both endpoints. The boundary-growth
inequality in `HsAdmissible` is a separate assertion.

The functions used here are the kernel and the actual sums of pair
potentials on their full carriers. No second Riesz kernel is introduced.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace Riesz1

/-- The positive coefficient of each Riesz pair. -/
theorem hsRiesz_pair_coefficient_pos (N : ℕ+) {β : ℝ} (hβ : 0 < β)
    (s : RieszExponent) : 0 < β * (N : ℝ) ^ (-s.val) := by
  exact mul_pos hβ (Real.rpow_pos_of_pos (by exact_mod_cast N.pos) _)

/-- The pair data for `H = 2 β N⁻ˢ ∑_{i<j} g(x_j-x_i)`. -/
def hsRieszPairPotentials (N : ℕ+) (β : ℝ) (hβ : 0 < β) (s : RieszExponent) :
    HsPairPotentials N (β * (N : ℝ) ^ (-s.val) * (s.val * (s.val + 1))) where
  potential := fun _ _ r => β * (N : ℝ) ^ (-s.val) * hurwitzKernel s.val r
  symmetric := fun _ _ => rfl
  smooth := fun _ _ _ =>
    contDiffOn_const.mul (contDiffOn_hurwitzKernel_unit s.val s.2.1 s.2.2)
  curvature := by
    intro i j hij r hr
    rw [deriv_const_mul_field', deriv_const_mul_field]
    exact mul_le_mul_of_nonneg_left (hurwitzKernel_curvature_lower s.val s.2.1 s.2.2 hr)
      (hsRiesz_pair_coefficient_pos N hβ s).le
  leftBoundary := fun _ _ _ =>
    (tendsto_hurwitzKernel_left s.val s.2.1 s.2.2).const_mul_atTop
      (hsRiesz_pair_coefficient_pos N hβ s)
  rightBoundary := fun _ _ _ =>
    (tendsto_hurwitzKernel_right s.val s.2.1 s.2.2).const_mul_atTop
      (hsRiesz_pair_coefficient_pos N hβ s)

theorem hsRieszPairPotentials_curvature_pos (N : ℕ+) {β : ℝ} (hβ : 0 < β)
    (s : RieszExponent) : 0 < β * (N : ℝ) ^ (-s.val) * (s.val * (s.val + 1)) := by
  exact mul_pos (hsRiesz_pair_coefficient_pos N hβ s) (mul_pos s.2.1 (by linarith [s.2.1]))

/-- Exact identification with the analytic representative, including its assigned
collision values. On the chamber only the restriction to `(0,1)` is evaluated. -/
theorem hsRieszPairPotentials_potential (N : ℕ+) (β : ℝ) (hβ : 0 < β)
    (s : RieszExponent) (i j : Fin (N : ℕ)) (r : ℝ) :
    (hsRieszPairPotentials N β hβ s).potential i j r =
      β * (N : ℝ) ^ (-s.val) * rieszRepresentative s r := rfl

/-- The renormalized limit is the potential used in the pair data. -/
theorem hsRieszPairPotentials_limit (N : ℕ+) (β : ℝ) (hβ : 0 < β)
    (s : RieszExponent) (i j : Fin (N : ℕ)) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun M : ℕ => β * (N : ℝ) ^ (-s.val) *
      ((∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), |(k : ℝ) + r| ^ (-s.val)) -
        2 * (M : ℝ) ^ (1 - s.val) / (1 - s.val))) atTop
      (𝓝 ((hsRieszPairPotentials N β hβ s).potential i j r)) := by
  exact ((fundamental_series s).1 r
    (coe_ne_zero_of_mem_Ioo_int 0 r (by simpa using hr))).const_mul _

theorem hsPairExpression_hsRieszPairPotentials (N : ℕ+) (β : ℝ) (hβ : 0 < β)
    (s : RieszExponent) (x : HsEuclidean N) :
    hsPairExpression (hsRieszPairPotentials N β hβ s) x =
      2 * β * (N : ℝ) ^ (-s.val) *
        ∑ i : Fin (N : ℕ), ∑ j ∈ Finset.univ.filter (i < ·),
          rieszRepresentative s ((x j - x i : ℝ) : UnitAddCircle) := by
  simp only [hsPairExpression, hsRieszPairPotentials_potential, ← Finset.mul_sum]
  ring

namespace Internal

theorem hs_convex_deriv2_nonneg {ψ : ℝ → ℝ}
    (hψ : ContDiffOn ℝ ∞ ψ (Ioo 0 1)) (hc : ConvexOn ℝ (Ioo (0 : ℝ) 1) ψ)
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) : 0 ≤ deriv (deriv ψ) r := by
  have hm := hc.monotoneOn_deriv (fun x hx =>
    (hψ.contDiffAt (isOpen_Ioo.mem_nhds hx)).differentiableAt (by norm_num))
  rw [← derivWithin_of_mem_nhds (isOpen_Ioo.mem_nhds hr)]
  exact hm.derivWithin_nonneg

theorem hs_convex_bounded_below {ψ : ℝ → ℝ}
    (hψ : ContDiffOn ℝ ∞ ψ (Ioo 0 1)) (hc : ConvexOn ℝ (Ioo (0 : ℝ) 1) ψ) :
    ∃ B : ℝ, ∀ r ∈ Ioo (0 : ℝ) 1, B ≤ ψ r := by
  refine ⟨ψ (1 / 2) - |deriv ψ (1 / 2)|, ?_⟩
  intro r hr
  exact hs_internal_convex_lower_bound hc
    ((hψ.contDiffAt (isOpen_Ioo.mem_nhds
      (by norm_num : (1 / 2 : ℝ) ∈ Ioo 0 1))).differentiableAt (by norm_num)) hr

end Internal

/-- Adding smooth convex unordered pairs preserves all the pair-potential requirements.
This part does not need bounded derivatives. Upper-triangular data `ψ i j` are extended
symmetrically by `min` and `max`. No symmetry assumption is imposed on unused data. -/
def HsPairPotentials.addConvex {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c)
    (ψ : Fin (N : ℕ) → Fin (N : ℕ) → ℝ → ℝ)
    (hψ : ∀ i j, i < j → ContDiffOn ℝ ∞ (ψ i j) (Ioo 0 1))
    (hcψ : ∀ i j, i < j → ConvexOn ℝ (Ioo (0 : ℝ) 1) (ψ i j)) :
    HsPairPotentials N c where
  potential := fun i j r => χ.potential i j r + ψ (min i j) (max i j) r
  symmetric := by
    intro i j
    rw [χ.symmetric i j, min_comm i j, max_comm i j]
  smooth := by
    intro i j hij
    simpa only [min_eq_left hij.le, max_eq_right hij.le] using
      (χ.smooth i j hij).add (hψ i j hij)
  curvature := by
    intro i j hij r hr
    simp only [min_eq_left hij.le, max_eq_right hij.le]
    have h₁ : ContDiffOn ℝ 1 (deriv (χ.potential i j)) (Ioo 0 1) :=
      (χ.smooth i j hij).deriv_of_isOpen isOpen_Ioo (by simp)
    have h₂ : ContDiffOn ℝ 1 (deriv (ψ i j)) (Ioo 0 1) :=
      (hψ i j hij).deriv_of_isOpen isOpen_Ioo (by simp)
    have he : deriv (fun r => χ.potential i j r + ψ i j r) =ᶠ[𝓝 r]
        fun r => deriv (χ.potential i j) r + deriv (ψ i j) r := by
      filter_upwards [isOpen_Ioo.mem_nhds hr] with z hz
      exact deriv_fun_add
        (((χ.smooth i j hij).contDiffAt (isOpen_Ioo.mem_nhds hz)).differentiableAt
          (by norm_num))
        (((hψ i j hij).contDiffAt (isOpen_Ioo.mem_nhds hz)).differentiableAt (by norm_num))
    rw [he.deriv_eq, deriv_fun_add
      ((h₁.contDiffAt (isOpen_Ioo.mem_nhds hr)).differentiableAt (by norm_num))
      ((h₂.contDiffAt (isOpen_Ioo.mem_nhds hr)).differentiableAt (by norm_num))]
    linarith [χ.curvature i j hij r hr,
      Internal.hs_convex_deriv2_nonneg (hψ i j hij) (hcψ i j hij) hr]
  leftBoundary := by
    intro i j hij
    simp only [min_eq_left hij.le, max_eq_right hij.le]
    obtain ⟨B, hB⟩ := Internal.hs_convex_bounded_below (hψ i j hij) (hcψ i j hij)
    apply tendsto_atTop_mono' (𝓝[>] (0 : ℝ)) _
      (tendsto_atTop_add_const_right _ B (χ.leftBoundary i j hij))
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with r hr0 hr1
    exact add_le_add_right (hB r ⟨hr0, hr1⟩) _
  rightBoundary := by
    intro i j hij
    simp only [min_eq_left hij.le, max_eq_right hij.le]
    obtain ⟨B, hB⟩ := Internal.hs_convex_bounded_below (hψ i j hij) (hcψ i j hij)
    apply tendsto_atTop_mono' (𝓝[<] (1 : ℝ)) _
      (tendsto_atTop_add_const_right _ B (χ.rightBoundary i j hij))
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))] with r hr1 hr0
    exact add_le_add_right (hB r ⟨hr0, hr1⟩) _

/-- Exact pair-sum identity for the perturbation. Its normalization is `2 ∑ ψ`. -/
theorem hsPairExpression_addConvex {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c)
    (ψ : Fin (N : ℕ) → Fin (N : ℕ) → ℝ → ℝ)
    (hψ : ∀ i j, i < j → ContDiffOn ℝ ∞ (ψ i j) (Ioo 0 1))
    (hcψ : ∀ i j, i < j → ConvexOn ℝ (Ioo (0 : ℝ) 1) (ψ i j))
    (x : HsEuclidean N) :
    hsPairExpression (χ.addConvex ψ hψ hcψ) x = hsPairExpression χ x +
      2 * ∑ i : Fin (N : ℕ), ∑ j ∈ Finset.univ.filter (i < ·), ψ i j (x j - x i) := by
  unfold hsPairExpression HsPairPotentials.addConvex
  simp only
  have he (i : Fin (N : ℕ)) :
      (∑ j ∈ Finset.univ.filter (i < ·),
        (χ.potential i j (x j - x i) + ψ (min i j) (max i j) (x j - x i))) =
      ∑ j ∈ Finset.univ.filter (i < ·),
        (χ.potential i j (x j - x i) + ψ i j (x j - x i)) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hij := (Finset.mem_filter.mp hj).2
    rw [min_eq_left hij.le, max_eq_right hij.le]
  simp_rw [he, Finset.sum_add_distrib]
  ring

end Riesz1

end
