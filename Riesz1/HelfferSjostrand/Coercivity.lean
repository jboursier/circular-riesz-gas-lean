/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.BoundaryCoreQuotient
public import Riesz1.HelfferSjostrand.VectorEnergySobolev
public import Riesz1.HelfferSjostrand.PoissonEquation
public import Riesz1.HelfferSjostrand.AnchoredInverseSpace

/-!
# The constant direction of the vector form

The scalar form core embeds into the vector completion by multiplication
by the unit rotation vector. This proves the first coercivity assertion of
Proposition 3.2, including membership for every scalar
Sobolev function. The anchored bound uses the existing anchored jet space.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace

namespace Riesz1

variable {N : ℕ+} {c : ℝ}

/-- Multiplication by the unit rotation direction, in the ambient jet space. -/
def hsRotationJet (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] :
    HsSobolev μ →L[ℝ] HsVectorJet μ :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.toContinuousLinearMap.comp
    (((PiLp.continuousLinearEquiv 2 ℝ _).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun i : Fin (N : ℕ) =>
        (hsUnitVector N i) • ContinuousLinearMap.id ℝ (HsSobolev μ))).prod 0)

theorem hsRotationJet_components (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ]
    (h : HsSobolev μ) (i : Fin (N : ℕ)) :
    (hsRotationJet μ h).ofLp.1 i = hsUnitVector N i • h := rfl

theorem hsRotationJet_energy (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ]
    (h : HsSobolev μ) : (hsRotationJet μ h).ofLp.2 = 0 := rfl

/-- Source tests give exactly the diagonal jet, with zero pair energy. -/
theorem hsRotationJet_test (χ : HsPairPotentials N c) (hN : 2 ≤ (N : ℕ)) (hc : 0 < c)
    (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ] (f : HsTestFunction N) :
    hsRotationJet μ (hsSobolevOfSmooth μ ⟨f.toFun, f.smoothOnClosure⟩) =
      hsVectorJet χ hN hc μ (fun i =>
        hsUnitVector N i • (⟨f.toFun, f.smooth, f.periodic, f.boundarySupport⟩ :
          hsTestSubmodule N)) := by
  apply (WithLp.equiv 2 _).injective
  apply Prod.ext
  · apply (WithLp.equiv 2 _).injective
    funext i
    exact (map_smul (hsTestSobolev μ) (hsUnitVector N i)
      ⟨f.toFun, f.smooth, f.periodic, f.boundarySupport⟩).symm
  · change 0 = (memLp_hsTestEnergyFun χ hN hc μ _).toLp _
    symm
    apply Lp.ext
    filter_upwards [(memLp_hsTestEnergyFun χ hN hc μ _).coeFn_toLp,
      Lp.coeFn_zero (EuclideanSpace ℝ (HsPairIndex N)) 2 μ] with y hy hz
    rw [hy, hz]
    ext p
    simp [hsTestEnergyFun, hsHessianEnergy, hsTestVector, hsUnitVector, hsRotationVector]

/-- The scalar form core puts every `he` in the actual vector space. -/
theorem hsRotationJet_mem (χ : HsPairPotentials N c) (hc : 0 < c) {C_N : ℝ}
    (hadm : HsAdmissible χ C_N)
    (h : HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))) :
    hsRotationJet _ h ∈ hsVectorSobolevSubmodule χ hadm.choose hc _ := by
  let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
  have hd := (scalar_boundary_core_L3219_quotient_real χ hc hadm).2.2.2
  have hclosed : IsClosed {h : HsSobolev μ |
      hsRotationJet μ h ∈ hsVectorSobolevSubmodule χ hadm.choose hc μ} :=
    (Submodule.isClosed_topologicalClosure _).preimage
      (hsRotationJet μ).continuous
  have hs : (hsSourceTestSobolev μ : Set (HsSobolev μ)) ⊆
      {h | hsRotationJet μ h ∈ hsVectorSobolevSubmodule χ hadm.choose hc μ} := by
    rintro _ ⟨f, rfl⟩
    change hsRotationJet μ (hsSobolevOfSmooth μ ⟨f.toFun, f.smoothOnClosure⟩) ∈
      hsVectorSobolevSubmodule χ hadm.choose hc μ
    rw [hsRotationJet_test χ hadm.choose hc μ f]
    exact hsVectorJet_mem_submodule χ hadm.choose hc μ _
  exact closure_minimal hs hclosed (hd h)

/-- Multiplication of a scalar Sobolev function by `e`, in the vector space. -/
def hsRotationField (χ : HsPairPotentials N c) (hc : 0 < c) {C_N : ℝ}
    (hadm : HsAdmissible χ C_N) :
    HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) →L[ℝ]
      HsVectorSobolev χ hadm.choose hc (hsQuotientGibbsProbability χ hc : Measure _) :=
  (hsRotationJet _).codRestrict _ (hsRotationJet_mem χ hc hadm)

theorem hsRotationField_value (χ : HsPairPotentials N c) (hc : 0 < c) {C_N : ℝ}
    (hadm : HsAdmissible χ C_N)
    (h : HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)))
    (i : Fin (N : ℕ)) :
    hsJetValue _ i (hsRotationField χ hc hadm h).val =
      hsUnitVector N i • hsSobolevValue _ h := by
  change hsSobolevValue _ (hsUnitVector N i • h) = _
  exact map_smul _ _ _

/-- The form of `he` is exactly the scalar Dirichlet energy. -/
theorem hsRotationField_form (χ : HsPairPotentials N c) (hc : 0 < c) {C_N : ℝ}
    (hadm : HsAdmissible χ C_N)
    (h k : HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))) :
    hsVectorSobolevForm χ hadm.choose hc _
      (hsRotationField χ hc hadm h) (hsRotationField χ hc hadm k) =
      hsDirichletForm _ h k := by
  have he : ∑ i : Fin (N : ℕ), (hsUnitVector N i) ^ 2 = 1 := by
    have hn := hsUnitVector_norm N
    have hs := EuclideanSpace.norm_sq_eq (hsUnitVector N)
    simp only [Real.norm_eq_abs, sq_abs] at hs
    rw [hn, one_pow] at hs
    exact hs.symm
  change (∑ i, inner ℝ (hsSobolevGradient _ (hsUnitVector N i • h))
    (hsSobolevGradient _ (hsUnitVector N i • k))) + inner ℝ (0 : Lp _ 2 _) 0 = _
  simp only [map_smul, real_inner_smul_left, real_inner_smul_right, inner_zero_right, add_zero]
  simp_rw [← mul_assoc, ← pow_two]
  rw [← Finset.sum_mul, he, one_mul]
  rfl

/-- The anchored coercivity clause of Proposition 3.2. -/
theorem anchored_vector_coercivity {n : ℕ} (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    : letI := isProbabilityMeasure_anchoredMeasureE χ hc
    ∀ u : AnchoredVectorSobolev χ (anchoredMeasureE χ),
    ‖anchoredInverseValues (anchoredMeasureE χ) u.val‖ ^ 2 ≤
      (2 * c)⁻¹ * anchoredVectorSobolevForm (anchoredMeasureE χ) u.val u.val := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  intro u
  have hb := anchoredInverse_value_bound (anchoredMeasureE χ) χ hc
    (ae_mem_anchoredSimplex χ) u
  rw [← real_inner_self_eq_norm_sq (x := anchoredInverseDerivatives (anchoredMeasureE χ) u.val),
    anchoredInverseDerivatives_inner] at hb
  exact (le_inv_mul_iff₀ (by positivity : 0 < 2 * c)).mpr hb

end Riesz1
