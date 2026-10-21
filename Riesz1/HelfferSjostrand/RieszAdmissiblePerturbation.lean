/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.RieszAdmissible

/-!
# Admissibility under smooth convex pair perturbations

Bounds on the first two
derivatives may be chosen separately for each unordered pair. Finiteness
of the label set supplies one bound in the proof. No symmetry is required
of the unused lower-triangular data.
-/

@[expose] public section

noncomputable section

open Set Filter Finset
open scoped Topology ContDiff

namespace Riesz1

theorem HsPairPotentials.deriv_addConvex {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c)
    (ψ : Fin (N : ℕ) → Fin (N : ℕ) → ℝ → ℝ)
    (hψ : ∀ i j, i < j → ContDiffOn ℝ ∞ (ψ i j) (Ioo 0 1))
    (hcψ : ∀ i j, i < j → ConvexOn ℝ (Ioo (0 : ℝ) 1) (ψ i j))
    {i j : Fin (N : ℕ)} (hij : i < j) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    deriv ((χ.addConvex ψ hψ hcψ).potential i j) r =
      deriv (χ.potential i j) r + deriv (ψ i j) r := by
  change deriv (fun r => χ.potential i j r + ψ (min i j) (max i j) r) r = _
  simp only [min_eq_left hij.le, max_eq_right hij.le]
  exact deriv_fun_add
    (((χ.smooth i j hij).contDiffAt (isOpen_Ioo.mem_nhds hr)).differentiableAt (by norm_num))
    (((hψ i j hij).contDiffAt (isOpen_Ioo.mem_nhds hr)).differentiableAt (by norm_num))

theorem HsPairPotentials.deriv2_addConvex {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c)
    (ψ : Fin (N : ℕ) → Fin (N : ℕ) → ℝ → ℝ)
    (hψ : ∀ i j, i < j → ContDiffOn ℝ ∞ (ψ i j) (Ioo 0 1))
    (hcψ : ∀ i j, i < j → ConvexOn ℝ (Ioo (0 : ℝ) 1) (ψ i j))
    {i j : Fin (N : ℕ)} (hij : i < j) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    deriv (deriv ((χ.addConvex ψ hψ hcψ).potential i j)) r =
      deriv (deriv (χ.potential i j)) r + deriv (deriv (ψ i j)) r := by
  have he : deriv ((χ.addConvex ψ hψ hcψ).potential i j) =ᶠ[𝓝 r]
      fun r => deriv (χ.potential i j) r + deriv (ψ i j) r := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with t ht
    exact χ.deriv_addConvex ψ hψ hcψ hij ht
  rw [he.deriv_eq]
  have h₁ : ContDiffOn ℝ 1 (deriv (χ.potential i j)) (Ioo 0 1) :=
    (χ.smooth i j hij).deriv_of_isOpen isOpen_Ioo (by simp)
  have h₂ : ContDiffOn ℝ 1 (deriv (ψ i j)) (Ioo 0 1) :=
    (hψ i j hij).deriv_of_isOpen isOpen_Ioo (by simp)
  exact deriv_fun_add
    ((h₁.contDiffAt (isOpen_Ioo.mem_nhds hr)).differentiableAt (by norm_num))
    ((h₂.contDiffAt (isOpen_Ioo.mem_nhds hr)).differentiableAt (by norm_num))

namespace Internal

theorem hs_pair_derivative_uniform_bound {N : ℕ+}
    (ψ : Fin (N : ℕ) → Fin (N : ℕ) → ℝ → ℝ)
    (hbound : ∀ i j, i < j → ∃ K : ℝ, ∀ r ∈ Ioo (0 : ℝ) 1,
      |deriv (ψ i j) r| ≤ K ∧ |deriv (deriv (ψ i j)) r| ≤ K) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i j, i < j → ∀ r ∈ Ioo (0 : ℝ) 1,
      |deriv (ψ i j) r| ≤ K ∧ |deriv (deriv (ψ i j)) r| ≤ K := by
  let ι := {p : Fin (N : ℕ) × Fin (N : ℕ) // p.1 < p.2}
  choose K hK using (fun p : ι => hbound p.val.1 p.val.2 p.property)
  obtain ⟨M, hM⟩ := Finite.exists_le K
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro i j hij r hr
  have hh := hK (⟨(i, j), hij⟩ : ι) r hr
  have hm := (hM (⟨(i, j), hij⟩ : ι)).trans (le_max_left M 0)
  exact ⟨hh.1.trans hm, hh.2.trans hm⟩

end Internal

/-- Admissibility with perturbation `P = 2 ∑_{i<j} ψᵢⱼ`.
The normalization agrees with `hsPairExpression_addConvex`. -/
theorem hsRiesz_perturbed_admissible (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (β : ℝ) (hβ : 0 < β) (s : RieszExponent)
    (ψ : Fin (N : ℕ) → Fin (N : ℕ) → ℝ → ℝ)
    (hψ : ∀ i j, i < j → ContDiffOn ℝ ∞ (ψ i j) (Ioo 0 1))
    (hcψ : ∀ i j, i < j → ConvexOn ℝ (Ioo (0 : ℝ) 1) (ψ i j))
    (hbound : ∀ i j, i < j → ∃ K : ℝ, ∀ r ∈ Ioo (0 : ℝ) 1,
      |deriv (ψ i j) r| ≤ K ∧ |deriv (deriv (ψ i j)) r| ≤ K) :
    ∃ C : ℝ, HsAdmissible ((hsRieszPairPotentials N β hβ s).addConvex ψ hψ hcψ) C := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hN
  have hN' : N = (n + 1).succPNat := by apply Subtype.ext; change (N : ℕ) = n + 1 + 1; omega
  subst N
  obtain ⟨K, hK, hKbound⟩ := Internal.hs_pair_derivative_uniform_bound ψ hbound
  let N := (n + 1).succPNat
  let A := β * (N : ℝ) ^ (-s.val)
  let χ := hsRieszPairPotentials N β hβ s
  have hA : 0 < A := hsRiesz_pair_coefficient_pos N hβ s
  have hη : 0 < (N : ℝ)⁻¹ := by positivity
  obtain ⟨b, B, hb, hB, hforce⟩ := hurwitzKernel_force_coercive s.val s.2.1 s.2.2 hη
  obtain ⟨D, hD, hcurv⟩ := hurwitzKernel_deriv2_gap_bound s.val s.2.1 s.2.2
  apply Internal.hs_admissible_of_pair_bounds n _ (hsRieszPairPotentials_curvature_pos N hβ s)
    s.2.1 (mul_pos hA hb) (add_nonneg (mul_nonneg hA.le hB) hK)
      (add_nonneg (mul_nonneg hA.le hD.le) hK)
  · intro i j hij r a hr ha₀ ha₁
    rw [HsPairPotentials.deriv_addConvex χ ψ hψ hcψ (i := i) (j := j) hij hr]
    change A * b * _ - (A * B + K) ≤
      (deriv (fun r => A * hurwitzKernel s.val r) r + deriv (ψ i j) r) * (r - a)
    rw [deriv_const_mul_field]
    have hh := mul_le_mul_of_nonneg_left (hforce a r ha₀ ha₁ hr) hA.le
    have ha : 0 < a ∧ a < 1 := ⟨lt_of_lt_of_le hη ha₀, by linarith⟩
    have hra : |r - a| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hr.1, hr.2]
    have hp : |deriv (ψ i j) r * (r - a)| ≤ K := by
      rw [abs_mul]
      exact (mul_le_mul (hKbound i j hij r hr).1 hra (abs_nonneg _) hK).trans_eq (mul_one K)
    have hp' := (abs_le.mp hp).1
    nlinarith
  · intro i j hij r δ hr hδ hδr hδr'
    rw [HsPairPotentials.deriv2_addConvex χ ψ hψ hcψ (i := i) (j := j) hij hr]
    change deriv (deriv (fun r => A * hurwitzKernel s.val r)) r +
      deriv (deriv (ψ i j)) r ≤ (A * D + K) * δ ^ (-s.val - 2)
    rw [deriv_const_mul_field', deriv_const_mul_field]
    have hh := mul_le_mul_of_nonneg_left (hcurv r δ hr hδ hδr hδr') hA.le
    have hp := (le_abs_self (deriv (deriv (ψ i j)) r)).trans (hKbound i j hij r hr).2
    have hpow : 1 ≤ δ ^ (-s.val - 2) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ (hδr.trans hr.2.le) (by linarith [s.2.1])
    have hm := le_mul_of_one_le_right hK hpow
    nlinarith

/-- Admissibility with the perturbation written literally as `∑_{i<j} ψᵢⱼ`.
Both admissibility constants and the pair-potential representation are existential. -/
theorem hsRiesz_add_pairSum_admissible (N : ℕ+) (hN : 2 ≤ (N : ℕ))
    (β : ℝ) (hβ : 0 < β) (s : RieszExponent)
    (ψ : Fin (N : ℕ) → Fin (N : ℕ) → ℝ → ℝ)
    (hψ : ∀ i j, i < j → ContDiffOn ℝ ∞ (ψ i j) (Ioo 0 1))
    (hcψ : ∀ i j, i < j → ConvexOn ℝ (Ioo (0 : ℝ) 1) (ψ i j))
    (hbound : ∀ i j, i < j → ∃ K : ℝ, ∀ r ∈ Ioo (0 : ℝ) 1,
      |deriv (ψ i j) r| ≤ K ∧ |deriv (deriv (ψ i j)) r| ≤ K) :
    ∃ c : ℝ, ∃ χ : HsPairPotentials N c, ∃ C : ℝ,
      HsAdmissible χ C ∧ ∀ x : HsEuclidean N,
        hsPairExpression χ x = 2 * β * (N : ℝ) ^ (-s.val) *
          (∑ i : Fin (N : ℕ), ∑ j ∈ univ.filter (i < ·),
            rieszRepresentative s ((x j - x i : ℝ) : UnitAddCircle)) +
          ∑ i : Fin (N : ℕ), ∑ j ∈ univ.filter (i < ·), ψ i j (x j - x i) := by
  let ψh := fun i j r => (1 / 2 : ℝ) * ψ i j r
  have hψh : ∀ i j, i < j → ContDiffOn ℝ ∞ (ψh i j) (Ioo 0 1) := by
    intro i j hij
    exact contDiffOn_const.mul (hψ i j hij)
  have hcψh : ∀ i j, i < j → ConvexOn ℝ (Ioo (0 : ℝ) 1) (ψh i j) := by
    intro i j hij
    exact (hcψ i j hij).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hboundh : ∀ i j, i < j → ∃ K : ℝ, ∀ r ∈ Ioo (0 : ℝ) 1,
      |deriv (ψh i j) r| ≤ K ∧ |deriv (deriv (ψh i j)) r| ≤ K := by
    intro i j hij
    obtain ⟨K, hK⟩ := hbound i j hij
    refine ⟨K / 2, ?_⟩
    intro r hr
    dsimp only [ψh]
    rw [deriv_const_mul_field', deriv_const_mul_field']
    dsimp only
    have hh := hK r hr
    constructor <;> rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] <;> linarith
  obtain ⟨C, hC⟩ := hsRiesz_perturbed_admissible N hN β hβ s ψh hψh hcψh hboundh
  refine ⟨_, (hsRieszPairPotentials N β hβ s).addConvex ψh hψh hcψh, C, hC, ?_⟩
  intro x
  rw [hsPairExpression_addConvex, hsPairExpression_hsRieszPairPotentials]
  dsimp only [ψh]
  simp only [← mul_sum]
  ring

end Riesz1

end
