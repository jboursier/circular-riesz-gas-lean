/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.ScalarPoincareProduct
public import Riesz1.HelfferSjostrand.ScalarPoincareAnchoredLaw
public import Riesz1.Frozen.Variance

/-!
# Scalar Poincaré for the Gibbs probability

Transport the smooth product estimate to the
configuration manifold and extend it to its actual Sobolev completion.
Only pair convexity is needed, so the boundary-growth condition of
admissibility is unnecessary. The sole external input is the Prékopa–Leindler inequality
`External.PrekopaLeindler`, taken as an explicit hypothesis.
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff InnerProductSpace ENNReal

namespace Riesz1

variable {N : ℕ+}

/-- The product law in any orthonormal radial chart. -/
theorem scalarPoincareConfig_map
    (basis : OrthonormalBasis (Fin (Module.finrank ℝ (hsOrthSubspace N))) ℝ (hsOrthSubspace N))
    {c : ℝ} (χ : HsPairPotentials N c) (hc : 0 < c) :
    (hsGibbsProbability χ hc : Measure (Configuration N)).map
      (fun X => ((scalarPoincareRadialChart basis).symm (hsConfigCoord N X).1,
        (hsConfigCoord N X).2)) =
      ((volume.restrict (scalarPoincareRadialDomain basis)).tilted
        (fun y => -scalarPoincareRadialPotential basis χ y)).prod
          (hsUniformCircle N : Measure _) := by
  let e := (scalarPoincareRadialChart basis).toHomeomorph.toMeasurableEquiv
  have hchart : (hsRadialProbability χ hc : Measure _).map e.symm =
      (volume.restrict (scalarPoincareRadialDomain basis)).tilted
        (fun y => -scalarPoincareRadialPotential basis χ y) := by
    rw [← scalarPoincareRadialChart_map basis χ hc]
    exact e.map_symm_map
  rw [show (fun X : Configuration N =>
      ((scalarPoincareRadialChart basis).symm (hsConfigCoord N X).1, (hsConfigCoord N X).2)) =
      (Prod.map e.symm id) ∘ hsConfigCoord N from rfl,
    ← Measure.map_map (e.symm.measurable.prodMap measurable_id) (measurable_hsConfigCoord N),
    hsGibbs_map_hsConfigCoord χ hc, ← Measure.map_prod_map _ _ e.symm.measurable measurable_id,
    hchart, Measure.map_id]

/-- **Scalar Poincaré on the Gibbs smooth core.** -/
theorem scalar_poincare_gibbs_smooth (hPL : External.PrekopaLeindler)
    (hN : 2 ≤ (N : ℕ)) {c : ℝ} (χ : HsPairPotentials N c) (hc : 0 < c)
    (f : hsSmoothCore N) :
    let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
    (∫ x, (hsSmoothValue f.val x - ∫ y, hsSmoothValue f.val y ∂μ) ^ 2 ∂μ) ≤
      hsPoincareConstant N c * ∫ x, ‖hsSmoothGradient f x‖ ^ 2 ∂μ := by
  let basis := stdOrthonormalBasis ℝ (hsOrthSubspace N)
  let ν := (volume.restrict (scalarPoincareRadialDomain basis)).tilted
    (fun y => -scalarPoincareRadialPotential basis χ y)
  let η : Measure (AddCircle (Real.sqrt (N : ℕ))) := hsUniformCircle N
  let coords := fun X : Configuration N =>
    ((scalarPoincareRadialChart basis).symm (hsConfigCoord N X).1, (hsConfigCoord N X).2)
  have hcoords : Measurable coords :=
    (((scalarPoincareRadialChart basis).symm.continuous.measurable.comp measurable_fst).prodMk
      measurable_snd).comp (measurable_hsConfigCoord N)
  let F := scalarPoincareProductExtension basis f.val
  let G := scalarPoincareProductExtension basis (gradient f.val)
  have hFm := (scalarPoincareProductExtension_properties basis f.val
    (f.property.2.choose_spec.2.2.continuousOn.mono f.property.2.choose_spec.2.1)).1
  have hGm := (scalarPoincareProductExtension_properties basis (gradient f.val)
    (scalarPoincare_gradient_continuousOn f.property)).1
  have htransport (K : EuclideanSpace ℝ (Fin (Module.finrank ℝ (hsOrthSubspace N))) ×
      AddCircle (Real.sqrt (N : ℕ)) → ℝ) (hK : StronglyMeasurable K) :
      (∫ p, K p ∂ν.prod η) =
        ∫ X, K (coords X) ∂(hsGibbsProbability χ hc : Measure (Configuration N)) := by
    rw [← scalarPoincareConfig_map basis χ hc]
    exact integral_map_of_stronglyMeasurable hcoords hK
  have hF (X : Configuration N) : F (coords X) = f.val (WithLp.toLp 2 X.val) :=
    scalarPoincareProductExtension_config basis f.val f.property.1 X
  have hG (X : Configuration N) : G (coords X) = gradient f.val (WithLp.toLp 2 X.val) :=
    scalarPoincareProductExtension_config basis (gradient f.val)
      (scalarPoincare_gradient_translate f.property) X
  have hm : (∫ p, F p ∂ν.prod η) =
      ∫ X, f.val (WithLp.toLp 2 X.val) ∂(hsGibbsProbability χ hc : Measure (Configuration N)) := by
    rw [htransport F hFm]
    exact integral_congr_ae (Eventually.of_forall hF)
  have hprod := scalar_poincare_product basis hPL hN χ hc f.property
  change (∫ p, (F p - ∫ q, F q ∂ν.prod η) ^ 2 ∂ν.prod η) ≤
    hsPoincareConstant N c * ∫ p, ‖G p‖ ^ 2 ∂ν.prod η at hprod
  rw [htransport (fun p => (F p - ∫ q, F q ∂ν.prod η) ^ 2)
      ((hFm.sub stronglyMeasurable_const).pow 2),
    htransport (fun p => ‖G p‖ ^ 2) (hGm.norm.pow 2), hm] at hprod
  simp only [hF, hG] at hprod
  dsimp only
  rw [hsQuotientGibbsProbability_eq_map,
    (measurableEmbedding_hsConfigurationMap N).integral_map,
    (measurableEmbedding_hsConfigurationMap N).integral_map,
    (measurableEmbedding_hsConfigurationMap N).integral_map]
  have he (X : Configuration N) : hsLiftPoint N (hsConfigurationMap N X) = WithLp.toLp 2 X.val := by
    change WithLp.toLp 2 ((hsConfigurationEquiv N).symm ((hsConfigurationEquiv N) X)).val = _
    rw [Equiv.symm_apply_apply]
  simpa only [hsSmoothValue, hsSmoothGradient, he] using hprod

/-- **Scalar Poincaré inequality** for the Gibbs measure, for every
element of `H¹(μ)`, with the exact constant. -/
theorem scalar_poincare_gibbs (hPL : External.PrekopaLeindler)
    (hN : 2 ≤ (N : ℕ)) {c : ℝ} (χ : HsPairPotentials N c) (hc : 0 < c)
    (f : HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))) :
    let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
    (∫ x, (hsSobolevValue μ f x - ∫ y, hsSobolevValue μ f y ∂μ) ^ 2 ∂μ) ≤
      hsPoincareConstant N c * ∫ x, ‖hsSobolevGradient μ f x‖ ^ 2 ∂μ :=
  Internal.hsPoincare_of_smooth _ (scalar_poincare_gibbs_smooth hPL hN χ hc) f

namespace Internal

/-- Conversion after square integrability has been established. -/
theorem hsPoincare_variance_of_real {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {F : Ω → ℝ} {G : Ω → E}
    (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) {C : ℝ} (hC : 0 ≤ C)
    (h : (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) ≤ C * ∫ x, ‖G x‖ ^ 2 ∂μ) :
    ∃ hFint : Integrable F μ,
      variance μ F hFint < ⊤ ∧
      (∫⁻ x, ENNReal.ofReal (‖G x‖ ^ 2) ∂μ) < ⊤ ∧
      variance μ F hFint ≤ ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (‖G x‖ ^ 2) ∂μ := by
  have hV := ofReal_integral_eq_lintegral_ofReal
    ((hF.sub (memLp_const (∫ y, F y ∂μ))).integrable_sq)
    (Eventually.of_forall fun _ => sq_nonneg _)
  have hE := ofReal_integral_eq_lintegral_ofReal hG.norm.integrable_sq
    (Eventually.of_forall fun _ => sq_nonneg _)
  simp only [Pi.sub_apply] at hV
  refine ⟨hF.integrable one_le_two, ?_, ?_, ?_⟩
  · rw [variance, ← hV]
    exact ENNReal.ofReal_lt_top
  · rw [← hE]
    exact ENNReal.ofReal_lt_top
  · rw [variance, ← hV, ← hE, ← ENNReal.ofReal_mul hC]
    exact ENNReal.ofReal_le_ofReal h

end Internal

/-- The scalar Poincaré inequality for the Gibbs measure, with the extended-real
variance. Finiteness is concluded for both nonnegative integrals. -/
theorem scalar_poincare_gibbs_variance (hPL : External.PrekopaLeindler)
    (hN : 2 ≤ (N : ℕ)) {c : ℝ} (χ : HsPairPotentials N c) (hc : 0 < c)
    (f : HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))) :
    let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
    ∃ hF : Integrable (hsSobolevValue μ f) μ,
      variance μ (hsSobolevValue μ f) hF < ⊤ ∧
      (∫⁻ x, ENNReal.ofReal (‖hsSobolevGradient μ f x‖ ^ 2) ∂μ) < ⊤ ∧
      variance μ (hsSobolevValue μ f) hF ≤ ENNReal.ofReal (hsPoincareConstant N c) *
        ∫⁻ x, ENNReal.ofReal (‖hsSobolevGradient μ f x‖ ^ 2) ∂μ :=
  Internal.hsPoincare_variance_of_real (Lp.memLp _) (Lp.memLp _)
    (hsPoincareConstant_pos N c).le (scalar_poincare_gibbs hPL hN χ hc f)

/-- The anchored clause of the scalar Poincaré inequality on `hsAnchoredLaw` in its
Euclidean coordinates, with extended-real variance and finiteness. -/
theorem scalar_poincare_anchoredLaw_variance (hPL : External.PrekopaLeindler)
    {n : ℕ} (hn : 0 < n) {c : ℝ} (χ : HsPairPotentials n.succPNat c) (hc : 0 < c)
    {F : AnchoredEuclidean n → ℝ} {G : AnchoredEuclidean n → AnchoredEuclidean n}
    (hFG : IsAnchoredH1 χ F G) :
    ∃ hF : Integrable F (anchoredMeasureE χ),
      variance (anchoredMeasureE χ) F hF < ⊤ ∧
      (∫⁻ y, ENNReal.ofReal (‖G y‖ ^ 2) ∂anchoredMeasureE χ) < ⊤ ∧
      variance (anchoredMeasureE χ) F hF ≤ ENNReal.ofReal ((2 * c)⁻¹) *
        ∫⁻ y, ENNReal.ofReal (‖G y‖ ^ 2) ∂anchoredMeasureE χ := by
  have := isProbabilityMeasure_anchoredMeasureE χ hc
  exact Internal.hsPoincare_variance_of_real hFG.1 hFG.2.1 (by positivity)
    (scalar_poincare_anchoredLaw hPL hn χ hc hFG)

end Riesz1

end
