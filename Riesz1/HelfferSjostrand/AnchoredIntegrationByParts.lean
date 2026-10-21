/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.AnchoredCalculus
public import Riesz1.HelfferSjostrand.AnchoredNeumannOperator

/-!
# Integration by parts for the anchored Langevin operator

This applies the variational definition of the Langevin operator
and the integration by parts identity to the Euclidean simplex. All compact
interior smooth tests and all elements of the Sobolev completion are allowed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Riesz1

variable {n : ℕ} {c : ℝ}

/-- Weighted integration by parts against a smooth anchored Sobolev core function. -/
theorem anchored_smooth_directional_integrationByParts (χ : HsPairPotentials n.succPNat c)
    {φ ψ : AnchoredEuclidean n → ℝ}
    (hφ : WeightedSobolev.SmoothNearClosure (anchoredSimplex n) φ)
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ anchoredSimplex n) (v : AnchoredEuclidean n) :
    ∫ y, ψ y * fderiv ℝ φ y v ∂anchoredMeasureE χ =
      ∫ y, φ y * (ψ y * fderiv ℝ (hsAnchoredHamiltonianE χ) y v - fderiv ℝ ψ y v)
        ∂anchoredMeasureE χ := by
  have hH := contDiffOn_hsAnchoredHamiltonianE χ
  have hw : ContDiffOn ℝ ∞ (fun y => Real.exp (-hsAnchoredHamiltonianE χ y))
      (anchoredSimplex n) := hH.neg.exp
  obtain ⟨W, _, hUW, hφW⟩ := hφ
  have hφU := hφW.mono (fun y hy => hUW (subset_closure hy))
  have hi := WeightedSobolev.integral_weighted_fderiv_of_compact_test
    (μ := volume) (isOpen_anchoredSimplex n) hψ hψc hψU hφU hw v
  have hz (y : AnchoredEuclidean n) (hy : y ∉ anchoredSimplex n) :
      ψ y = 0 ∧ fderiv ℝ ψ y = 0 := by
    have hs : y ∉ tsupport ψ := fun h => hy (hψU h)
    exact ⟨image_eq_zero_of_notMem_tsupport hs, fderiv_of_notMem_tsupport ℝ hs⟩
  rw [anchoredMeasureE_integral, anchoredMeasureE_integral]
  congr 1
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
    simp only [(hz y hy).1, zero_mul, mul_zero]),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
      simp only [(hz y hy).1, (hz y hy).2, zero_apply, zero_mul, sub_zero, mul_zero])]
  calc
    _ = ∫ y, (ψ y * Real.exp (-hsAnchoredHamiltonianE χ y)) * fderiv ℝ φ y v := by
      apply integral_congr_ae
      filter_upwards with y
      ring
    _ = _ := hi
    _ = _ := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards with y
      by_cases hy : y ∈ anchoredSimplex n
      · have hdH := (hH.contDiffAt ((isOpen_anchoredSimplex n).mem_nhds hy)
          ).differentiableAt (by norm_num)
        have hd := ((hψ.differentiable (by norm_num) y).hasFDerivAt.mul
          hdH.hasFDerivAt.neg.exp).fderiv
        change fderiv ℝ (fun z => ψ z * Real.exp (-hsAnchoredHamiltonianE χ z)) y = _ at hd
        rw [hd]
        simp only [Pi.neg_apply, add_apply, smul_apply, neg_apply, smul_eq_mul]
        ring
      · have hs : y ∉ tsupport (fun z => ψ z * Real.exp (-hsAnchoredHamiltonianE χ z)) :=
          fun h => hy (hψU (tsupport_mul_subset_left h))
        simp only [fderiv_of_notMem_tsupport ℝ hs, zero_apply, mul_zero, neg_zero,
          (hz y hy).1, (hz y hy).2, zero_mul, sub_zero]

/-- The anchored weighted weak-gradient identity, against every compact interior test. -/
theorem anchoredH1_directional_integrationByParts (χ : HsPairPotentials n.succPNat c)
    (hc : 0 < c) {F : AnchoredEuclidean n → ℝ} {G : AnchoredEuclidean n → AnchoredEuclidean n}
    (hFG : IsAnchoredH1 χ F G) {ψ : AnchoredEuclidean n → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ anchoredSimplex n) (v : AnchoredEuclidean n) :
    ∫ y, ψ y * inner ℝ (G y) v ∂anchoredMeasureE χ =
      ∫ y, F y * (ψ y * fderiv ℝ (hsAnchoredHamiltonianE χ) y v - fderiv ℝ ψ y v)
        ∂anchoredMeasureE χ := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  have ht : MemLp (fun y => ψ y • v) 2 (anchoredMeasureE χ) :=
    (hψ.continuous.smul continuous_const).memLp_of_hasCompactSupport
      (hψc.smul_right)
  have hq := memLp_anchoredCoefficient χ hc hψ hψc hψU v
  simpa only [inner_smul_right] using WeightedSobolev.Internal.pairing_of_smooth
    (isBounded_anchoredSimplex n) (ae_mem_anchoredSimplex χ) ht hq
    (fun φ hφ => by
      simpa only [inner_smul_right, inner_gradient_left] using
        anchored_smooth_directional_integrationByParts χ hφ hψ hψc hψU v) hFG

/-- The anchored Langevin expression is the sum of its directional contributions. -/
theorem anchoredLangevinExpr_eq_sum (χ : HsPairPotentials n.succPNat c)
    {f : AnchoredEuclidean n → ℝ} (hf : ContDiff ℝ ∞ f)
    {ι : Type*} [Fintype ι] (B : OrthonormalBasis ι ℝ (AnchoredEuclidean n))
    (y : AnchoredEuclidean n) :
    anchoredLangevinExpr χ f y = ∑ i,
      (fderiv ℝ f y (B i) * fderiv ℝ (hsAnchoredHamiltonianE χ) y (B i) -
        fderiv ℝ (fun z => fderiv ℝ f z (B i)) y (B i)) := by
  have hdd := (contDiff_infty_iff_fderiv.mp hf).2.differentiable (by norm_num)
  have hdiag (v : AnchoredEuclidean n) :
      fderiv ℝ (fun z => fderiv ℝ f z v) y v = iteratedFDeriv ℝ 2 f y ![v, v] := by
    rw [fderiv_clm_apply (hdd y) (differentiableAt_const v), iteratedFDeriv_two_apply]
    simp
  change inner ℝ (gradient (hsAnchoredHamiltonianE χ) y) (gradient f y) -
    Laplacian.laplacian f y = _
  have hin : inner ℝ (gradient (hsAnchoredHamiltonianE χ) y) (gradient f y) =
      ∑ i, inner ℝ (gradient f y) (B i) * inner ℝ (B i) (gradient (hsAnchoredHamiltonianE χ) y) :=
    (real_inner_comm _ _).trans (B.sum_inner_mul_inner _ _).symm
  rw [hin,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f B,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_comm (gradient (hsAnchoredHamiltonianE χ) y) (B i), inner_gradient_left,
    inner_gradient_left, hdiag]

/-- The anchored differential expression has finite square norm on every source test. -/
theorem memLp_anchoredLangevinExpr (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    {f : AnchoredEuclidean n → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hfU : tsupport f ⊆ anchoredSimplex n) :
    MemLp (anchoredLangevinExpr χ f) 2 (anchoredMeasureE χ) := by
  let B := stdOrthonormalBasis ℝ (AnchoredEuclidean n)
  have hsum : anchoredLangevinExpr χ f = fun y => ∑ i,
      (fderiv ℝ f y (B i) * fderiv ℝ (hsAnchoredHamiltonianE χ) y (B i) -
        fderiv ℝ (fun z => fderiv ℝ f z (B i)) y (B i)) :=
    funext (anchoredLangevinExpr_eq_sum χ hf B)
  rw [hsum]
  apply memLp_finsetSum
  intro i _
  exact memLp_anchoredCoefficient χ hc
    ((contDiff_infty_iff_fderiv.mp hf).2.clm_apply contDiff_const)
    (hfc.fderiv_apply ℝ (B i)) ((tsupport_fderiv_apply_subset ℝ (B i)).trans hfU) (B i)

/-- Integration by parts for the full anchored Sobolev completion. -/
theorem anchoredIntegrationByParts (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    {f : AnchoredEuclidean n → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hfU : tsupport f ⊆ anchoredSimplex n)
    {F : AnchoredEuclidean n → ℝ} {G : AnchoredEuclidean n → AnchoredEuclidean n}
    (hFG : IsAnchoredH1 χ F G) :
    ∫ y, anchoredLangevinExpr χ f y * F y ∂anchoredMeasureE χ =
      ∫ y, inner ℝ (gradient f y) (G y) ∂anchoredMeasureE χ := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  let B := stdOrthonormalBasis ℝ (AnchoredEuclidean n)
  let a := fun i y => fderiv ℝ f y (B i)
  let b := fun i y => a i y * fderiv ℝ (hsAnchoredHamiltonianE χ) y (B i) -
    fderiv ℝ (a i) y (B i)
  have ha i : MemLp (a i) 2 (anchoredMeasureE χ) :=
    ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
      ).memLp_of_hasCompactSupport (hfc.fderiv_apply ℝ (B i))
  have hb i : MemLp (b i) 2 (anchoredMeasureE χ) := memLp_anchoredCoefficient χ hc
    ((contDiff_infty_iff_fderiv.mp hf).2.clm_apply contDiff_const)
    (hfc.fderiv_apply ℝ (B i)) ((tsupport_fderiv_apply_subset ℝ (B i)).trans hfU) (B i)
  have hs y : inner ℝ (gradient f y) (G y) = ∑ i, a i y * inner ℝ (G y) (B i) := by
    rw [← B.sum_inner_mul_inner (gradient f y) (G y)]
    apply Finset.sum_congr rfl
    intro i _
    rw [real_inner_comm (G y) (B i), inner_gradient_left]
  calc
    _ = ∫ y, ∑ i, F y * b i y ∂anchoredMeasureE χ := by
      apply integral_congr_ae
      filter_upwards with y
      rw [anchoredLangevinExpr_eq_sum χ hf B y, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    _ = ∑ i, ∫ y, F y * b i y ∂anchoredMeasureE χ :=
      integral_finsetSum _ (fun i _ => hFG.1.integrable_mul (hb i))
    _ = ∑ i, ∫ y, a i y * inner ℝ (G y) (B i) ∂anchoredMeasureE χ := by
      apply Finset.sum_congr rfl
      intro i _
      exact (anchoredH1_directional_integrationByParts χ hc hFG
        ((contDiff_infty_iff_fderiv.mp hf).2.clm_apply contDiff_const)
        (hfc.fderiv_apply ℝ (B i)) ((tsupport_fderiv_apply_subset ℝ (B i)).trans hfU) (B i)).symm
    _ = ∫ y, ∑ i, a i y * inner ℝ (G y) (B i) ∂anchoredMeasureE χ :=
      (integral_finsetSum _ (fun i _ => (ha i).integrable_mul (hFG.2.1.inner_const (B i)))).symm
    _ = _ := integral_congr_ae (ae_of_all _ fun y => (hs y).symm)

/-- The anchored Langevin relation depends only on the three almost everywhere classes. -/
theorem isAnchoredLangevin_congr (χ : HsPairPotentials n.succPNat c)
    {F F' A A' : AnchoredEuclidean n → ℝ} {G G' : AnchoredEuclidean n → AnchoredEuclidean n}
    (h : IsAnchoredLangevin χ F G A) (hF : F =ᵐ[anchoredMeasureE χ] F')
    (hG : G =ᵐ[anchoredMeasureE χ] G') (hA : A =ᵐ[anchoredMeasureE χ] A') :
    IsAnchoredLangevin χ F' G' A' := by
  refine ⟨WeightedSobolev.IsWeightedH1.congr h.1 hF hG, h.2.1.ae_eq hA, ?_⟩
  intro H K hHK
  calc
    _ = ∫ y, inner ℝ (G y) (K y) ∂anchoredMeasureE χ :=
      integral_congr_ae (hG.mono fun y hy => by dsimp only; rw [hy])
    _ = _ := h.2.2 H K hHK
    _ = _ := integral_congr_ae (hA.mono fun y hy => by dsimp only; rw [hy])

/-- Every source test belongs to the anchored Neumann graph with its Langevin expression. -/
theorem isAnchoredLangevin_of_testFunction (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    {f : AnchoredEuclidean n → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hfU : tsupport f ⊆ anchoredSimplex n) :
    IsAnchoredLangevin χ f (gradient f) (anchoredLangevinExpr χ f) := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  exact ⟨isAnchoredH1_of_testFunction χ f hf hfc inferInstance,
    memLp_anchoredLangevinExpr χ hc hf hfc hfU,
    fun F G hFG => (anchoredIntegrationByParts χ hc hf hfc hfU hFG).symm⟩

/-- The test function as a point of the anchored Sobolev completion. -/
def anchoredSobolevOfTest (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    (f : AnchoredEuclidean n → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    AnchoredSobolev χ := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  have h := isAnchoredH1_of_testFunction χ f hf hfc inferInstance
  refine ⟨(h.1.toLp f, h.2.1.toLp (gradient f)), ?_⟩
  exact WeightedSobolev.IsWeightedH1.congr h h.1.coeFn_toLp.symm h.2.1.coeFn_toLp.symm

/-- Every compact interior smooth test is in the full anchored Neumann domain. -/
def anchoredNeumannOfTest (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    (f : AnchoredEuclidean n → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hfU : tsupport f ⊆ anchoredSimplex n) : anchoredNeumannDomain χ := by
  let h := isAnchoredLangevin_of_testFunction χ hc hf hfc hfU
  refine ⟨anchoredSobolevOfTest χ hc f hf hfc, h.2.1.toLp (anchoredLangevinExpr χ f), ?_⟩
  refine ⟨(anchoredSobolevOfTest χ hc f hf hfc).property, Lp.memLp _, ?_⟩
  exact (isAnchoredLangevin_congr χ h h.1.1.coeFn_toLp.symm
    h.1.2.1.coeFn_toLp.symm h.2.1.coeFn_toLp.symm).2.2

/-- Agreement of the function-valued anchored operator with its differential expression. -/
theorem anchoredNeumannOperator_of_test (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    (f : AnchoredEuclidean n → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hfU : tsupport f ⊆ anchoredSimplex n) :
    anchoredNeumannOperator χ (anchoredNeumannOfTest χ hc f hf hfc hfU) =
      (memLp_anchoredLangevinExpr χ hc hf hfc hfU).toLp (anchoredLangevinExpr χ f) := by
  apply (anchoredNeumannOperator_eq_iff χ hc _ _).mpr
  have h := isAnchoredLangevin_of_testFunction χ hc hf hfc hfU
  exact isAnchoredLangevin_congr χ h h.1.1.coeFn_toLp.symm
    h.1.2.1.coeFn_toLp.symm h.2.1.coeFn_toLp.symm

end Riesz1

end
