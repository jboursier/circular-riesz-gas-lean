/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.AnchoredLawSobolev
public import Riesz1.ToMathlib.WeightedSobolev.LocalIntegrationByParts
public import Riesz1.ToMathlib.WeightedSobolev.VariationalPairing

/-!
# Interior calculus for the anchored Gibbs density

The Euclidean simplex is bounded, the anchored Hamiltonian is smooth
inside it, and integration against its law is normalized weighted Lebesgue
integration. These facts require no boundary growth condition.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Riesz1

variable {n : ℕ} {c : ℝ}

/-- The anchored Euclidean simplex is bounded, including the zero dimensional case. -/
theorem isBounded_anchoredSimplex (n : ℕ) : Bornology.IsBounded (anchoredSimplex n) := by
  have hbox : anchoredSimplex n ⊆
      (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).symm '' Icc (fun _ => 0) (fun _ => 1) := by
    intro y hy
    refine ⟨WithLp.ofLp y, ⟨?_, ?_⟩, rfl⟩
    · exact fun i => (hy.1 i).1.le
    · exact fun i => (hy.1 i).2.le
  exact ((isCompact_Icc.image (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).symm.continuous
    ).isBounded).subset hbox

/-- Smoothness of the anchored Hamiltonian on the entire open simplex. -/
theorem contDiffOn_hsAnchoredHamiltonianE (χ : HsPairPotentials n.succPNat c) :
    ContDiffOn ℝ ∞ (hsAnchoredHamiltonianE χ) (anchoredSimplex n) := by
  unfold hsAnchoredHamiltonianE hsAnchoredHamiltonian hsPairExpression
  apply ContDiffOn.mul contDiffOn_const
  apply ContDiffOn.sum
  intro i _
  apply ContDiffOn.sum
  intro j hj
  have hij : i < j := (Finset.mem_filter.mp hj).2
  have ha (k : Fin (n.succPNat : ℕ)) :
      ContDiff ℝ ∞ (fun y : AnchoredEuclidean n => anchorVector (WithLp.ofLp y) k) := by
    induction k using Fin.cases with
    | zero =>
      change ContDiff ℝ ∞ (fun _ : AnchoredEuclidean n => (0 : ℝ))
      exact contDiff_const
    | succ l =>
      change ContDiff ℝ ∞ (fun y : AnchoredEuclidean n => y l)
      exact (EuclideanSpace.proj (𝕜 := ℝ) l).contDiff
  exact (χ.smooth i j hij).comp ((ha j).sub (ha i)).contDiffOn
    (fun y hy => anchorVector_sub_mem_Ioo hy hij)

/-- Exact normalized anchored integration in the Euclidean simplex. -/
theorem anchoredMeasureE_integral (χ : HsPairPotentials n.succPNat c)
    (f : AnchoredEuclidean n → ℝ) :
    ∫ y, f y ∂anchoredMeasureE χ = ((hsPartitionFunction χ)⁻¹).toReal *
      ∫ y in anchoredSimplex n, Real.exp (-hsAnchoredHamiltonianE χ y) * f y := by
  unfold anchoredMeasureE
  have heTo : MeasurableEmbedding (WithLp.toLp 2 : (Fin n → ℝ) → AnchoredEuclidean n) :=
    (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).symm.measurableEmbedding
  rw [heTo.integral_map]
  rw [hsAnchoredLaw, integral_smul_measure, ← hsPartitionFunction_eq_hsAnchoredWeight,
    hsAnchoredWeight, integral_withDensity_eq_integral_toReal_smul₀ (aemeasurable_hsAnchoredDensity χ)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have hm := ((PiLp.volume_preserving_ofLp (Fin n)).restrict_preimage
    (measurableSet_anchoredDomain n)).map_eq
  have he : MeasurableEmbedding (WithLp.ofLp : AnchoredEuclidean n → (Fin n → ℝ)) :=
    (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).measurableEmbedding
  congr 1
  rw [← hm, he.integral_map]
  apply integral_congr_ae
  filter_upwards with y
  simp only [hsAnchoredDensity, ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
  rfl

/-- The localized directional Langevin coefficient is continuous on the ambient space. -/
theorem continuous_anchoredCoefficient (χ : HsPairPotentials n.succPNat c)
    {ψ : AnchoredEuclidean n → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψU : tsupport ψ ⊆ anchoredSimplex n) (v : AnchoredEuclidean n) :
    Continuous (fun y => ψ y * fderiv ℝ (hsAnchoredHamiltonianE χ) y v - fderiv ℝ ψ y v) := by
  have hH := (contDiffOn_hsAnchoredHamiltonianE χ).continuousOn_fderiv_of_isOpen
    (isOpen_anchoredSimplex n) (by norm_num)
  exact (WeightedSobolev.continuous_cutoff_mul (isOpen_anchoredSimplex n) hψ.continuous hψU
    (hH.clm_apply continuousOn_const)).sub
      ((hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const)

/-- The localized directional coefficient has finite weighted square norm. -/
theorem memLp_anchoredCoefficient (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    {ψ : AnchoredEuclidean n → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ anchoredSimplex n)
    (v : AnchoredEuclidean n) :
    MemLp (fun y => ψ y * fderiv ℝ (hsAnchoredHamiltonianE χ) y v - fderiv ℝ ψ y v)
      2 (anchoredMeasureE χ) := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  exact (continuous_anchoredCoefficient χ hψ hψU v).memLp_of_hasCompactSupport
    (hψc.mul_right.sub (hψc.fderiv_apply ℝ v))

end Riesz1

end
