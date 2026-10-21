/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.SettingGibbs
public import Riesz1.HelfferSjostrand.IntegrationByPartsConsequences
public import Riesz1.HelfferSjostrand.RieszAdmissiblePairs
public import Riesz1.Variance.LoopForceEnergy
public import Riesz1.Variance.LoopIBPHS
public import Riesz1.Frozen.GibbsMeasure
public import Riesz1.Frozen.ParametersExponent

/-!
# Transfer of the Helffer–Sjöstrand integration by parts to the Gibbs law

The Riesz pair Hamiltonian on the cyclic quotient is `β` times the energy. Hence the
quotient Gibbs probability `rieszProb P N` is the push-forward of the Gibbs law
`gibbsMeasure P N` under the fundamental-region projection (`rieszProb_eq_map`). Integrals against
`rieszProb P N` therefore become integrals against `gibbsMeasure P N` (`integral_rieszProb`).

Combining this transfer with the Helffer–Sjöstrand integration by parts on the quotient gives
`rieszIBP`. It states the integration by parts identity for the Riesz Gibbs law and a
smooth periodic test function `G`, with no hypothesis beyond smoothness and periodicity of `G`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1

/-- The pair data of the Riesz Hamiltonian `H = β × energy` on the cyclic quotient. -/
def rieszPairs (P : Parameters) (N : ℕ+) :=
  hsRieszPairPotentials N P.val.1 P.property.1 (parametersExponent P)

/-- The quotient Gibbs probability of the Riesz pair data. -/
def rieszProb (P : Parameters) (N : ℕ+) : ProbabilityMeasure (HsConfiguration N) :=
  hsQuotientGibbsProbability (rieszPairs P N)
    (hsRieszPairPotentials_curvature_pos N P.property.1 (parametersExponent P))

/-- The quotient Hamiltonian of the Riesz pair data equals `β` times the energy. -/
theorem hsHamiltonian_rieszPairs (P : Parameters) (N : ℕ+) (x : HsConfiguration N) :
    hsHamiltonian (rieszPairs P N) x = hsRieszHamiltonian P N x := by
  unfold hsHamiltonian hsFundamentalHamiltonian rieszPairs hsRieszHamiltonian
  rw [hsPairExpression_hsRieszPairPotentials_eq_energyLift, WithLp.ofLp_toLp,
    energy_eq_energyLift]

/-- The quotient Riesz Gibbs probability is the push-forward of the Gibbs law. -/
theorem rieszProb_eq_map (P : Parameters) (N : ℕ+) :
    (rieszProb P N : Measure (HsConfiguration N)) =
      (gibbsMeasure P N).map (hsConfigurationMap N) := by
  have hH : hsHamiltonian (rieszPairs P N) = hsRieszHamiltonian P N :=
    funext (hsHamiltonian_rieszPairs P N)
  have hZ : hsPartitionFunction (rieszPairs P N) =
      ∫⁻ x, ENNReal.ofReal (Real.exp (-hsRieszHamiltonian P N x))
        ∂hsConfigurationVolume N := by
    rw [hsPartitionFunction_eq_quotient_integral, hH]
  rw [← hsRieszGibbsMeasure_eq_map]
  show (hsPartitionFunction (rieszPairs P N))⁻¹ • hsGibbsWeight (rieszPairs P N) = _
  rw [hZ, hsGibbsWeight, hH]

/-- Integrals against the quotient Riesz Gibbs probability are integrals of the lifted
function against the Gibbs law. -/
theorem integral_rieszProb (P : Parameters) (N : ℕ+) {F : HsConfiguration N → ℝ} :
    ∫ x, F x ∂(rieszProb P N : Measure (HsConfiguration N)) =
      ∫ X, F (hsConfigurationMap N X) ∂gibbsMeasure P N := by
  rw [rieszProb_eq_map]
  exact (measurableEmbedding_hsConfigurationMap N).integral_map F

/-- The Euclidean lift of the image of a configuration is its ordered real lift. -/
theorem hsLiftPoint_configurationMap (N : ℕ+) (X : Configuration N) :
    hsLiftPoint N (hsConfigurationMap N X) = WithLp.toLp 2 X.val := by
  have h : (hsConfigurationEquiv N).symm (hsConfigurationMap N X) = X :=
    (hsConfigurationEquiv N).symm_apply_apply X
  unfold hsLiftPoint
  rw [h]

/-- The scalar Langevin expression at a quotient point whose fundamental representative
is `X`. -/
theorem hsLangevin_eq_of_symm {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c)
    (f : HsTestFunction N) (x : HsConfiguration N) (X : Configuration N)
    (h : (hsConfigurationEquiv N).symm x = X) :
    hsLangevin χ f x =
      hsLangevinLift χ f ⟨WithLp.toLp 2 X.val, ⟨X.property.1, X.property.2.2.2⟩⟩ := by
  subst h
  rfl

/-- The scalar Langevin expression at the image of a configuration, written in Euclidean
coordinates of its ordered real lift. -/
theorem hsLangevin_configurationMap {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c)
    (f : HsTestFunction N) (X : Configuration N) :
    hsLangevin χ f (hsConfigurationMap N X) =
      inner ℝ (gradient (hsPairExpression χ) (WithLp.toLp 2 X.val))
          (gradient f.toFun (WithLp.toLp 2 X.val)) -
        Laplacian.laplacian f.toFun (WithLp.toLp 2 X.val) := by
  have h : (hsConfigurationEquiv N).symm (hsConfigurationMap N X) = X :=
    (hsConfigurationEquiv N).symm_apply_apply X
  exact hsLangevin_eq_of_symm χ f (hsConfigurationMap N X) X h

/-- Integration by parts on the quotient, for the Gibbs probability `hsQuotientGibbsProbability`
and a smooth periodic lift `G`: the Langevin pairing with `G` equals the energy pairing of the
gradients. This is the Helffer–Sjöstrand identity transported to lifted coordinates. -/
theorem hsIntegrationByParts_lift {N : ℕ+} {c : ℝ} (hN : 2 ≤ (N : ℕ))
    (χ : HsPairPotentials N c) (hc : 0 < c) (f : HsTestFunction N)
    (G : HsEuclidean N → ℝ) (hG : HsSmoothOnClosure N G) :
    ∫ x, hsLangevin χ f x * G (hsLiftPoint N x)
        ∂(hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) =
      ∫ x, inner ℝ (gradient f.toFun (hsLiftPoint N x)) (gradient G (hsLiftPoint N x))
        ∂(hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) := by
  have hIBP := hsIntegrationByParts_form hN χ hc f (hsSobolevOfSmooth _ ⟨G, hG⟩)
  rw [hsDirichletForm_eq_integral] at hIBP
  have hval : (hsSobolevValue (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))
      (hsSobolevOfSmooth _ ⟨G, hG⟩) : HsConfiguration N → ℝ) =ᵐ[
        (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))]
      hsSmoothValue G :=
    (hG.memLp_value _).coeFn_toLp
  have hgG : (hsSobolevGradient (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))
      (hsSobolevOfSmooth _ ⟨G, hG⟩) : HsConfiguration N → HsEuclidean N) =ᵐ[
        (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))]
      hsSmoothGradient ⟨G, hG⟩ :=
    (hG.memLp_gradient _).coeFn_toLp
  have hgf : (hsSobolevGradient (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))
      (hsSobolevOfSmooth _ ⟨f.toFun, f.smoothOnClosure⟩) :
        HsConfiguration N → HsEuclidean N) =ᵐ[
        (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))]
      hsSmoothGradient ⟨f.toFun, f.smoothOnClosure⟩ :=
    (f.smoothOnClosure.memLp_gradient _).coeFn_toLp
  have hL : ∫ x, hsLangevin χ f x * G (hsLiftPoint N x)
        ∂(hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) =
      ∫ x, hsLangevin χ f x * hsSobolevValue
          (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))
          (hsSobolevOfSmooth _ ⟨G, hG⟩) x
        ∂(hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) := by
    apply integral_congr_ae
    filter_upwards [hval] with x hx
    rw [hx]
    rfl
  have hR : ∫ x, inner ℝ (gradient f.toFun (hsLiftPoint N x)) (gradient G (hsLiftPoint N x))
        ∂(hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) =
      ∫ x, inner ℝ (hsSobolevGradient
          (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))
          (hsSobolevOfSmooth _ ⟨f.toFun, f.smoothOnClosure⟩) x)
        (hsSobolevGradient
          (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))
          (hsSobolevOfSmooth _ ⟨G, hG⟩) x)
        ∂(hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) := by
    apply integral_congr_ae
    filter_upwards [hgf, hgG] with x hx1 hx2
    rw [hx1, hx2]
    rfl
  rw [hL, hR]
  exact hIBP

/-- Integration by parts for the Riesz Gibbs law. For every smooth periodic test function
`f` on the quotient and every smooth periodic function `G`, with `N ≥ 2`, the Langevin pairing
of `f` with `G` under `gibbsMeasure P N` equals the gradient pairing of `f` and `G`. -/
theorem rieszIBP (P : Parameters) (N : ℕ+) (hN : 2 ≤ (N : ℕ)) (f : HsTestFunction N)
    (G : HsEuclidean N → ℝ) (hG : ContDiff ℝ ∞ G)
    (hGper : ∀ (k : ℤ) (x : HsEuclidean N), G (hsTranslate (k : ℝ) x) = G x) :
    ∫ X : Configuration N,
        (inner ℝ (gradient (hsPairExpression (rieszPairs P N)) (WithLp.toLp 2 X.val))
            (gradient f.toFun (WithLp.toLp 2 X.val)) -
          Laplacian.laplacian f.toFun (WithLp.toLp 2 X.val)) * G (WithLp.toLp 2 X.val)
        ∂gibbsMeasure P N =
      ∫ X : Configuration N, inner ℝ (gradient f.toFun (WithLp.toLp 2 X.val))
          (gradient G (WithLp.toLp 2 X.val)) ∂gibbsMeasure P N := by
  have hL := hsIntegrationByParts_lift hN (rieszPairs P N)
    (hsRieszPairPotentials_curvature_pos N P.property.1 (parametersExponent P)) f G
    ⟨hGper, univ, isOpen_univ, subset_univ _, hG.contDiffOn⟩
  calc ∫ X : Configuration N,
          (inner ℝ (gradient (hsPairExpression (rieszPairs P N)) (WithLp.toLp 2 X.val))
              (gradient f.toFun (WithLp.toLp 2 X.val)) -
            Laplacian.laplacian f.toFun (WithLp.toLp 2 X.val)) * G (WithLp.toLp 2 X.val)
          ∂gibbsMeasure P N
      = ∫ X : Configuration N, hsLangevin (rieszPairs P N) f (hsConfigurationMap N X) *
          G (hsLiftPoint N (hsConfigurationMap N X)) ∂gibbsMeasure P N := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
        simp only [hsLangevin_configurationMap, hsLiftPoint_configurationMap]
    _ = ∫ x, hsLangevin (rieszPairs P N) f x * G (hsLiftPoint N x)
          ∂(rieszProb P N : Measure (HsConfiguration N)) :=
        (integral_rieszProb P N (F := fun x =>
          hsLangevin (rieszPairs P N) f x * G (hsLiftPoint N x))).symm
    _ = ∫ x, inner ℝ (gradient f.toFun (hsLiftPoint N x)) (gradient G (hsLiftPoint N x))
          ∂(rieszProb P N : Measure (HsConfiguration N)) := hL
    _ = ∫ X : Configuration N, inner ℝ (gradient f.toFun (WithLp.toLp 2 X.val))
          (gradient G (WithLp.toLp 2 X.val)) ∂gibbsMeasure P N := by
        refine (integral_rieszProb P N (F := fun x =>
          inner ℝ (gradient f.toFun (hsLiftPoint N x)) (gradient G (hsLiftPoint N x)))).trans ?_
        refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
        simp only [hsLiftPoint_configurationMap]

end Riesz1

end
