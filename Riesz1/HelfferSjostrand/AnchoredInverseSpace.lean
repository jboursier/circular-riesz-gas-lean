/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.VectorEnergyAnchoredSobolev
public import Riesz1.HelfferSjostrand.BLQuadratic

/-!
# Coercivity of the anchored vector form

The value and derivative--Hessian projections of the vector jet space
give its norm decomposition. The pairs incident to the pinned particle give
coercivity, first on test tuples and then on their closure. This is the vector
existence ingredient of Remark 3.2.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set InnerProductSpace
open scoped Topology

namespace Riesz1

variable {n : ℕ} {c : ℝ} (μ : Measure (AnchoredEuclidean n)) [IsFiniteMeasure μ]

/-- The vector of values of an anchored jet. -/
def anchoredInverseValues : Lp (AnchoredJetPoint n) 2 μ →L[ℝ]
    Lp (AnchoredEuclidean n) 2 μ :=
  (WithLp.fstL 2 ℝ (AnchoredEuclidean n) (AnchoredJetPair n)).compLpL 2 μ

/-- The gradients and the pair Hessian energy of an anchored jet. -/
def anchoredInverseDerivatives : Lp (AnchoredJetPoint n) 2 μ →L[ℝ]
    Lp (AnchoredJetPair n) 2 μ := jetPairL.compLpL 2 μ

omit [IsFiniteMeasure μ] in
/-- The squared vector-jet norm splits into value and form energy. -/
theorem anchoredInverse_norm_sq (u : Lp (AnchoredJetPoint n) 2 μ) :
    ‖u‖ ^ 2 = ‖anchoredInverseValues μ u‖ ^ 2 +
      ‖anchoredInverseDerivatives μ u‖ ^ 2 := by
  simp_rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  rw [← integral_add (L2.integrable_inner _ _) (L2.integrable_inner _ _)]
  apply integral_congr_ae
  filter_upwards [ContinuousLinearMap.coeFn_compLpL
      (WithLp.fstL 2 ℝ (AnchoredEuclidean n) (AnchoredJetPair n)) u,
    ContinuousLinearMap.coeFn_compLpL jetPairL u] with y hv hd
  change inner ℝ (u y) (u y) = _
  dsimp only [anchoredInverseValues, anchoredInverseDerivatives]
  rw [hv, hd]
  exact WithLp.prod_inner_apply _ _

/-- The remainder inner product is precisely the vector form. -/
theorem anchoredInverseDerivatives_inner (u v : Lp (AnchoredJetPoint n) 2 μ) :
    inner ℝ (anchoredInverseDerivatives μ u) (anchoredInverseDerivatives μ v) =
      anchoredVectorSobolevForm μ u v := by
  unfold anchoredVectorSobolevForm
  simp_rw [L2.inner_def]
  rw [← integral_finsetSum _ (fun i _ => L2.integrable_inner _ _),
    ← integral_add (integrable_finsetSum _ (fun i _ => L2.integrable_inner _ _))
      (L2.integrable_inner _ _)]
  apply integral_congr_ae
  have hg (w : Lp (AnchoredJetPoint n) 2 μ) (i : Fin n) :=
    ContinuousLinearMap.coeFn_compLpL (jetGradL i) w
  filter_upwards [ContinuousLinearMap.coeFn_compLpL jetPairL u,
    ContinuousLinearMap.coeFn_compLpL jetPairL v,
    ae_all_iff.mpr (hg u), ae_all_iff.mpr (hg v),
    ContinuousLinearMap.coeFn_compLpL jetEnergyVecL u,
    ContinuousLinearMap.coeFn_compLpL jetEnergyVecL v] with y hu hv hgu hgv heu hev
  change inner ℝ (anchoredInverseDerivatives μ u y) (anchoredInverseDerivatives μ v y) = _
  dsimp only [anchoredInverseDerivatives, anchoredJetGrad, anchoredJetEnergyVec]
  rw [hu, hv]
  simp_rw [hgu, hgv, heu, hev]
  exact (WithLp.prod_inner_apply _ _).trans (by rw [PiLp.inner_apply]; rfl)

/-- The anchored lift preserves the Euclidean norm. -/
theorem norm_anchorLift (b : AnchoredEuclidean n) : ‖anchorLift n b‖ = ‖b‖ := by
  have hs : ‖anchorLift n b‖ ^ 2 = ‖b‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, anchorLift_apply]
    change (∑ x : Fin (n + 1), ‖anchorVector b.ofLp x‖ ^ 2) = _
    rw [Fin.sum_univ_succ]
    simp [anchorVector]
  nlinarith [norm_nonneg (anchorLift n b), norm_nonneg b]

/-- Uniform anchored curvature, in the actual `n` Euclidean coordinates. -/
theorem anchoredHessianEnergy_lower (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    {y : AnchoredEuclidean n} (hy : y ∈ anchoredSimplex n) (b : AnchoredEuclidean n) :
    2 * c * ‖b‖ ^ 2 ≤ ‖anchoredHessianEnergy χ y b‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq (x := anchoredHessianEnergy χ y b), inner_anchoredHessianEnergy χ hc
    (anchorLift_mem_chamber hy), fderiv_fderiv_hsAnchoredHamiltonianE χ
      (anchorLift_mem_chamber hy)]
  have hb : anchorLift n b ⟨0, n.succPNat.pos⟩ = 0 := by
    simp [anchorLift_apply, anchorVector]
  simpa only [norm_anchorLift] using
    hessian_hsPairExpression_first_lower χ hc (anchorLift_mem_chamber hy) (anchorLift n b) hb

/-- The value projection of a test jet is its test vector, almost everywhere. -/
theorem anchoredInverseValues_jet_ae (χ : HsPairPotentials n.succPNat c)
    (u : AnchoredVectorTest n) :
    (anchoredInverseValues μ (anchoredVectorJet χ μ u) :
      AnchoredEuclidean n → AnchoredEuclidean n) =ᵐ[μ] anchoredTestVector u := by
  filter_upwards [ContinuousLinearMap.coeFn_compLpL
    (WithLp.fstL 2 ℝ (AnchoredEuclidean n) (AnchoredJetPair n)) (anchoredVectorJet χ μ u),
    (memLp_anchoredJetFun χ μ u).coeFn_toLp] with y h1 h2
  dsimp only [anchoredInverseValues]
  rw [h1]
  change (anchoredVectorJet χ μ u : AnchoredEuclidean n → AnchoredJetPoint n) y = _ at h2
  rw [h2]
  rfl

/-- Curvature controls the value norm of every test tuple. -/
theorem anchoredInverse_test_bound (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    (hμ : ∀ᵐ y ∂μ, y ∈ anchoredSimplex n) (u : AnchoredVectorTest n) :
    2 * c * ‖anchoredInverseValues μ (anchoredVectorJet χ μ u)‖ ^ 2 ≤
      ‖anchoredInverseDerivatives μ (anchoredVectorJet χ μ u)‖ ^ 2 := by
  have hv : (anchoredInverseValues μ (anchoredVectorJet χ μ u) :
      AnchoredEuclidean n → AnchoredEuclidean n) =ᵐ[μ] anchoredTestVector u :=
    anchoredInverseValues_jet_ae μ χ u
  have hd : (anchoredInverseDerivatives μ (anchoredVectorJet χ μ u) :
      AnchoredEuclidean n → AnchoredJetPair n) =ᵐ[μ]
      fun y => WithLp.toLp 2
        (WithLp.toLp 2 (fun i => gradient (u i : AnchoredEuclidean n → ℝ) y),
          anchoredEnergyFun χ u y) := by
    filter_upwards [ContinuousLinearMap.coeFn_compLpL jetPairL (anchoredVectorJet χ μ u),
      (memLp_anchoredJetFun χ μ u).coeFn_toLp] with y h1 h2
    dsimp only [anchoredInverseDerivatives]
    rw [h1]
    change (anchoredVectorJet χ μ u : AnchoredEuclidean n → AnchoredJetPoint n) y = _ at h2
    rw [h2]
    rfl
  simp_rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  rw [← integral_const_mul]
  apply integral_mono_ae ((L2.integrable_inner _ _).const_mul _) (L2.integrable_inner _ _)
  filter_upwards [hμ, hv, hd] with y hy hyv hyd
  rw [hyv, hyd, real_inner_self_eq_norm_sq, WithLp.prod_inner_apply]
  have he := anchoredHessianEnergy_lower χ hc hy (anchoredTestVector u y)
  change 2 * c * ‖anchoredTestVector u y‖ ^ 2 ≤ _ + _
  rw [real_inner_self_eq_norm_sq (x := anchoredEnergyFun χ u y)]
  exact he.trans (le_add_of_nonneg_left (real_inner_self_nonneg))

/-- Curvature controls every element of the completed vector space. -/
theorem anchoredInverse_value_bound (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    (hμ : ∀ᵐ y ∂μ, y ∈ anchoredSimplex n) (u : AnchoredVectorSobolev χ μ) :
    2 * c * ‖anchoredInverseValues μ u.val‖ ^ 2 ≤
      ‖anchoredInverseDerivatives μ u.val‖ ^ 2 := by
  have hclosed : IsClosed {w : Lp (AnchoredJetPoint n) 2 μ |
      2 * c * ‖anchoredInverseValues μ w‖ ^ 2 ≤
        ‖anchoredInverseDerivatives μ w‖ ^ 2} :=
    isClosed_le (continuous_const.mul ((anchoredInverseValues μ).continuous.norm.pow 2))
      ((anchoredInverseDerivatives μ).continuous.norm.pow 2)
  apply closure_minimal (s := (LinearMap.range (anchoredVectorJetLin χ μ) : Set _))
      (fun w hw => ?_) hclosed
      (show u.val ∈ closure (LinearMap.range (anchoredVectorJetLin χ μ) : Set _) from u.property)
  obtain ⟨t, rfl⟩ := hw
  exact anchoredInverse_test_bound μ χ hc hμ t

/-- The gradients and Hessian energy on the closed vector space. -/
def anchoredInverseDifferential (χ : HsPairPotentials n.succPNat c) :
    AnchoredVectorSobolev χ μ →L[ℝ] Lp (AnchoredJetPair n) 2 μ :=
  (anchoredInverseDerivatives μ).comp (anchoredVectorSobolevSubmodule χ μ).subtypeL

/-- The continuous bilinear vector form, with the normalization of `anchoredVectorSobolevForm`. -/
def anchoredInverseBilinear (χ : HsPairPotentials n.succPNat c) :
    AnchoredVectorSobolev χ μ →L[ℝ] AnchoredVectorSobolev χ μ →L[ℝ] ℝ := by
  let G := anchoredInverseDifferential μ χ
  exact (innerSL ℝ).bilinearComp G G

/-- The bilinear form is the existing completed form, rather than a new energy. -/
theorem anchoredInverseBilinear_eq (χ : HsPairPotentials n.succPNat c)
    (u v : AnchoredVectorSobolev χ μ) :
    anchoredInverseBilinear μ χ u v = anchoredVectorSobolevForm μ u.val v.val := by
  exact anchoredInverseDerivatives_inner μ u.val v.val

/-- Coercivity in the full vector-jet norm. No compatibility condition is needed. -/
theorem anchoredInverseBilinear_coercive (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    (hμ : ∀ᵐ y ∂μ, y ∈ anchoredSimplex n) :
    IsCoercive (anchoredInverseBilinear μ χ) := by
  let k := 2 * c / (1 + 2 * c)
  have hk : 0 < k := div_pos (by linarith) (by linarith)
  refine ⟨k, hk, fun u => ?_⟩
  change k * ‖u‖ * ‖u‖ ≤ inner ℝ
    (anchoredInverseDerivatives μ u.val) (anchoredInverseDerivatives μ u.val)
  rw [real_inner_self_eq_norm_sq]
  have hv := anchoredInverse_value_bound μ χ hc hμ u
  have hn := anchoredInverse_norm_sq μ u.val
  have he : k * (1 + 2 * c) = 2 * c := div_mul_cancel₀ _ (by linarith)
  have hle : k ≤ 1 := (div_le_one (by linarith : 0 < 1 + 2 * c)).mpr (by linarith)
  change k * ‖u.val‖ * ‖u.val‖ ≤ _
  nlinarith [mul_nonneg (sub_nonneg.mpr hle)
    (sq_nonneg ‖anchoredInverseDerivatives μ u.val‖), mul_le_mul_of_nonneg_left hv hk.le]

end Riesz1

end
