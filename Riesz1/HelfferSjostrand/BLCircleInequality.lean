/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.BLEuclidean
public import Riesz1.HelfferSjostrand.BlockConcentrationTransport
public import Riesz1.HelfferSjostrand.ScalarPoincareGibbs
public import Riesz1.HelfferSjostrand.NonGradientGapFactorization
public import Riesz1.Externals.PrekopaLeindlerProof

/-!
# Brascamp–Lieb on the circle

Orthogonal radial and rotation coordinates split the Gibbs probability into a radial
law and a uniform circle. A rotation invariant Sobolev observable depends only on the
radial variable. Applying the Euclidean Brascamp–Lieb inequality to almost every
rotation slice gives the inequality with the Hessian inverted on the mean zero hyperplane.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Submodule
open scoped ContDiff InnerProductSpace

namespace Riesz1

variable {N : ℕ+} {c : ℝ}

/-- The Hessian restricted to the hyperplane orthogonal to common rotations. -/
def blCircleHessian (χ : HsPairPotentials N c) (x : HsConfiguration N) :
    hsOrthSubspace N →L[ℝ] hsOrthSubspace N →L[ℝ] ℝ :=
  (fderiv ℝ (fderiv ℝ (hsPairExpression χ)) (hsLiftPoint N x)).bilinearComp
    (hsOrthSubspace N).subtypeL (hsOrthSubspace N).subtypeL

private theorem blCircleHessian_lower (χ : HsPairPotentials N c)
    (x : HsConfiguration N) (u : hsOrthSubspace N) :
    2 * c * N * ‖u‖ ^ 2 ≤ blCircleHessian χ x u u := by
  exact hessian_hsPairExpression_lower_bound χ (hsLiftPoint_mem_chamber N x) u
    (mem_orthogonal_singleton_iff_inner_left.mp u.property)

private theorem blCircleHessian_coercive (χ : HsPairPotentials N c) (hc : 0 < c)
    (x : HsConfiguration N) : IsCoercive (blCircleHessian χ x) :=
  ⟨2 * c * N, by positivity, fun u => by
    simpa only [pow_two, mul_assoc] using blCircleHessian_lower χ x u⟩

/-- The inverse of the Hessian on the mean zero hyperplane, extended by zero on the
common rotation direction. -/
def blCircleInverseHessian (χ : HsPairPotentials N c) (hc : 0 < c)
    (x : HsConfiguration N) : HsEuclidean N →L[ℝ] HsEuclidean N :=
  let hB : IsCoercive (blCircleHessian χ x) :=
    ⟨2 * c * N, by positivity, fun u => by
      change 2 * c * N * ‖(u : HsEuclidean N)‖ * ‖(u : HsEuclidean N)‖ ≤
        fderiv ℝ (fderiv ℝ (hsPairExpression χ)) (hsLiftPoint N x) u u
      simpa only [pow_two, mul_assoc] using
        hessian_hsPairExpression_lower_bound χ (hsLiftPoint_mem_chamber N x) u
          (mem_orthogonal_singleton_iff_inner_left.mp u.property)⟩
  (hsOrthSubspace N).subtypeL.comp
    (hB.continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp
      (hsOrthSubspace N).orthogonalProjectionOnto)

private def blCircleEnergy (χ : HsPairPotentials N c) (x : HsConfiguration N)
    (g : HsEuclidean N) : ℝ :=
  sSup (Set.range fun u : hsOrthSubspace N =>
    2 * inner ℝ g (u : HsEuclidean N) - blCircleHessian χ x u u)

private theorem blCircleEnergy_eq_inverse (χ : HsPairPotentials N c) (hc : 0 < c)
    (x : HsConfiguration N) (g : HsEuclidean N) :
    blCircleEnergy χ x g = inner ℝ g (blCircleInverseHessian χ hc x g) := by
  let P := (hsOrthSubspace N).orthogonalProjectionOnto
  have he : blCircleEnergy χ x g = sSup (Set.range fun u : hsOrthSubspace N =>
      2 * inner ℝ (P g) u - blCircleHessian χ x u u) := by
    simp only [blCircleEnergy, P, inner_orthogonalProjectionOnto_eq_of_mem_right]
  rw [he, bl_quadratic_sSup_eq_inverse (blCircleHessian_coercive χ hc x)]
  · exact inner_orthogonalProjectionOnto_eq_of_mem_right _ _
  · intro u v
    exact ((hsPairExpression_contDiffOn χ).contDiffAt
      ((isOpen_hsChamber N).mem_nhds (hsLiftPoint_mem_chamber N x))).isSymmSndFDerivAt
        (by simp) u v

private theorem blCircleEnergy_integrable (χ : HsPairPotentials N c) (hc : 0 < c)
    {μ : Measure (HsConfiguration N)} (G : HsConfiguration N → HsEuclidean N)
    (hG : MemLp G 2 μ) : Integrable (fun x => blCircleEnergy χ x (G x)) μ := by
  let P := (hsOrthSubspace N).orthogonalProjectionOnto
  let g := hG.aestronglyMeasurable.mk G
  have hg : Measurable g := hG.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  obtain ⟨D, hD⟩ := TopologicalSpace.exists_dense_seq (hsOrthSubspace N)
  have hm (u : hsOrthSubspace N) : Measurable (fun x => blCircleHessian χ x u u) :=
    (measurable_fderiv_fderiv_apply (hsPairExpression χ) (u : HsEuclidean N)).comp
      (measurable_hsLiftPoint N)
  have hmeas : Measurable (fun x => ⨆ n,
      2 * inner ℝ (g x) (D n : HsEuclidean N) - blCircleHessian χ x (D n) (D n)) :=
    Measurable.iSup fun n =>
      (((continuous_id.inner continuous_const).measurable.comp hg).const_mul 2).sub (hm (D n))
  have hbound (x : HsConfiguration N) (v : HsEuclidean N) :=
    bl_variational_energy_bounds (blCircleHessian χ x) (P v)
      (show 0 < 2 * c * (N : ℝ) by positivity) (blCircleHessian_lower χ x)
  have he (x : HsConfiguration N) (v : HsEuclidean N) :
      blCircleEnergy χ x v = sSup (Set.range fun u : hsOrthSubspace N =>
        2 * inner ℝ (P v) u - blCircleHessian χ x u u) := by
    simp only [blCircleEnergy, P, inner_orthogonalProjectionOnto_eq_of_mem_right]
  have hQm : AEMeasurable (fun x => blCircleEnergy χ x (G x)) μ := by
    apply hmeas.aemeasurable.congr
    filter_upwards [hG.aestronglyMeasurable.ae_eq_mk] with x hx
    rw [hx]
    apply Eq.symm
    apply sSup_range_eq_iSup_dense (by fun_prop) _ hD
    refine ⟨‖P (g x)‖ ^ 2 / (2 * c * N), ?_⟩
    rintro _ ⟨u, rfl⟩
    change 2 * inner ℝ (g x) (u : HsEuclidean N) - blCircleHessian χ x u u ≤ _
    rw [← inner_orthogonalProjectionOnto_eq_of_mem_right u (g x)]
    exact bl_quadratic_le_norm_sq_div (by positivity) (blCircleHessian_lower χ x) (P (g x)) u
  apply (hG.norm.integrable_sq.div_const (2 * c * N)).mono' hQm.aestronglyMeasurable
  filter_upwards [] with x
  obtain ⟨h0, h1⟩ := hbound x (G x)
  rw [← he] at h0 h1
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  apply h1.trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact pow_le_pow_left₀ (norm_nonneg _)
    ((hsOrthSubspace N).norm_orthogonalProjectionOnto_apply_le _) 2

variable (basis : OrthonormalBasis (Fin (Module.finrank ℝ (hsOrthSubspace N))) ℝ
  (hsOrthSubspace N))

private theorem blCircle_coord_radial (x : HsConfiguration N) :
    scalarPoincareRadialEmbedding basis (blockQuotientProductCoord basis x).1 =
      hsOrthProj N (hsLiftPoint N x) := by
  change ((scalarPoincareRadialChart basis)
    ((scalarPoincareRadialChart basis).symm (hsOrthComp N (hsLiftPoint N x))) :
      HsEuclidean N) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

private theorem blCircle_coord_map (χ : HsPairPotentials N c) (hc : 0 < c) :
    (hsQuotientGibbsProbability χ hc : Measure _).map (blockQuotientProductCoord basis) =
      ((volume.restrict (scalarPoincareRadialDomain basis)).tilted
        (fun y => -scalarPoincareRadialPotential basis χ y)).prod AddCircle.haarAddCircle := by
  rw [hsQuotientGibbsProbability_eq_map,
    Measure.map_map (measurableEmbedding_blockQuotientProductCoord basis).measurable
      (measurable_hsConfigurationMap N)]
  have he : blockQuotientProductCoord basis ∘ hsConfigurationMap N =
      (fun X => ((scalarPoincareRadialChart basis).symm (hsConfigCoord N X).1,
        (hsConfigCoord N X).2)) := by
    funext X
    simp only [Function.comp_def, blockQuotientProductCoord,
      show hsConfigurationMap N = hsConfigurationEquiv N from rfl,
      Equiv.symm_apply_apply]
  rw [he, scalarPoincareConfig_map basis χ hc]
  rfl

private theorem blCircle_radialGradient_inner (g : HsEuclidean N)
    (u : EuclideanSpace ℝ (Fin (Module.finrank ℝ (hsOrthSubspace N)))) :
    inner ℝ (blockRadialGradientMap basis g) u =
      inner ℝ g (scalarPoincareRadialEmbedding basis u) := by
  rw [← (scalarPoincareRadialChart basis).inner_map_map,
    blockRadialGradientMap_apply, LinearIsometryEquiv.apply_symm_apply]
  change inner ℝ (hsOrthComp N g) (scalarPoincareRadialChart basis u) = _
  have hP : hsOrthComp N g = (hsOrthSubspace N).orthogonalProjectionOnto g := by
    apply Subtype.ext
    exact (orthComponent_eq_starProjection (hsUnitVector_norm N) g).trans
      (Submodule.coe_orthogonalProjectionOnto_apply _ g).symm
  rw [hP, inner_orthogonalProjectionOnto_eq_of_mem_right]
  rfl

private theorem blCircle_coord_hessian (χ : HsPairPotentials N c)
    (x : HsConfiguration N)
    (u v : EuclideanSpace ℝ (Fin (Module.finrank ℝ (hsOrthSubspace N)))) :
    fderiv ℝ (fderiv ℝ (scalarPoincareRadialPotential basis χ))
        (blockQuotientProductCoord basis x).1 u v =
      blCircleHessian χ x (scalarPoincareRadialChart basis u)
        (scalarPoincareRadialChart basis v) := by
  have hx : (blockQuotientProductCoord basis x).1 ∈ scalarPoincareRadialDomain basis := by
    change scalarPoincareRadialEmbedding basis _ ∈ hsChamber N
    rw [blCircle_coord_radial, hsOrthProj_eq_translate]
    exact (hsTranslate_mem_chamber_iff _ _).mpr (hsLiftPoint_mem_chamber N x)
  rw [hessian_scalarPoincareRadialPotential basis χ hx,
    blCircle_coord_radial, hsOrthProj_eq_translate,
    fderiv_fderiv_hsPairExpression χ ((hsTranslate_mem_chamber_iff _ _).mpr
      (hsLiftPoint_mem_chamber N x))]
  change hsPairHessian χ (hsTranslate _ (hsLiftPoint N x))
      (scalarPoincareRadialEmbedding basis u) (scalarPoincareRadialEmbedding basis v) =
    fderiv ℝ (fderiv ℝ (hsPairExpression χ)) (hsLiftPoint N x)
      (scalarPoincareRadialEmbedding basis u) (scalarPoincareRadialEmbedding basis v)
  rw [fderiv_fderiv_hsPairExpression χ (hsLiftPoint_mem_chamber N x)]
  simp only [hsPairHessian, hsTranslate_apply, add_sub_add_right_eq_sub]

private theorem blCircle_coord_energy (χ : HsPairPotentials N c)
    (x : HsConfiguration N) (g : HsEuclidean N) :
    sSup (Set.range fun u : EuclideanSpace ℝ (Fin (Module.finrank ℝ (hsOrthSubspace N))) =>
      2 * inner ℝ (blockRadialGradientMap basis g) u -
        fderiv ℝ (fderiv ℝ (scalarPoincareRadialPotential basis χ))
          (blockQuotientProductCoord basis x).1 u u) = blCircleEnergy χ x g := by
  simp_rw [blCircle_coord_hessian basis χ x, blCircle_radialGradient_inner]
  exact congrArg sSup ((scalarPoincareRadialChart basis).surjective.range_comp
    (fun u : hsOrthSubspace N => 2 * inner ℝ g (u : HsEuclidean N) - blCircleHessian χ x u u))

private theorem blCircle_product_bound (hN : 2 ≤ (N : ℕ))
    (χ : HsPairPotentials N c) (hc : 0 < c)
    {F : EuclideanSpace ℝ (Fin (Module.finrank ℝ (hsOrthSubspace N))) ×
      AddCircle (Real.sqrt (N : ℕ)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (Module.finrank ℝ (hsOrthSubspace N))) ×
      AddCircle (Real.sqrt (N : ℕ)) → HsEuclidean N}
    (hFG : WeightedSobolev.IsGraphH1
      (((volume.restrict (scalarPoincareRadialDomain basis)).tilted
        (fun q => -scalarPoincareRadialPotential basis χ q)).prod AddCircle.haarAddCircle)
      (fun _ : hsSmoothCore N => True) (fun f => scalarPoincareProductExtension basis f.val)
      (fun f => scalarPoincareProductExtension basis (gradient f.val)) F G)
    {f : EuclideanSpace ℝ (Fin (Module.finrank ℝ (hsOrthSubspace N))) → ℝ}
    (hrep : F =ᵐ[(((volume.restrict (scalarPoincareRadialDomain basis)).tilted
      (fun q => -scalarPoincareRadialPotential basis χ q)).prod AddCircle.haarAddCircle)]
      (fun p => f p.1))
    (hQ : Integrable (fun p => sSup (Set.range fun u =>
      2 * inner ℝ (blockRadialGradientMap basis (G p)) u -
        fderiv ℝ (fderiv ℝ (scalarPoincareRadialPotential basis χ)) p.1 u u))
      (((volume.restrict (scalarPoincareRadialDomain basis)).tilted
        (fun q => -scalarPoincareRadialPotential basis χ q)).prod AddCircle.haarAddCircle)) :
    let ρ := ((volume.restrict (scalarPoincareRadialDomain basis)).tilted
      (fun q => -scalarPoincareRadialPotential basis χ q)).prod AddCircle.haarAddCircle
    (∫ p, (F p - ∫ r, F r ∂ρ) ^ 2 ∂ρ) ≤
      ∫ p, sSup (Set.range fun u => 2 * inner ℝ (blockRadialGradientMap basis (G p)) u -
        fderiv ℝ (fderiv ℝ (scalarPoincareRadialPotential basis χ)) p.1 u u) ∂ρ := by
  let ν := (volume.restrict (scalarPoincareRadialDomain basis)).tilted
    (fun q => -scalarPoincareRadialPotential basis χ q)
  let η : Measure (AddCircle (Real.sqrt (N : ℕ))) := AddCircle.haarAddCircle
  have : IsProbabilityMeasure ν := scalarPoincareRadial_isProbabilityMeasure basis χ hc
  have hν := scalarPoincareRadial_ae_mem basis χ
  have hs := Internal.block_product_ae_radial_slice basis ν hν hFG
  have hr := Measure.ae_ae_of_ae_prod
    (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hrep)
  let Q := fun p => sSup (Set.range fun u =>
    2 * inner ℝ (blockRadialGradientMap basis (G p)) u -
      fderiv ℝ (fderiv ℝ (scalarPoincareRadialPotential basis χ)) p.1 u u)
  have hsbound : ∀ᵐ w ∂η,
      (∫ q, (f q - ∫ r, f r ∂ν) ^ 2 ∂ν) ≤ ∫ q, Q (q, w) ∂ν := by
    filter_upwards [hs, hr] with w hw hwr
    have hfg := hw.congr hwr (Eventually.of_forall fun _ => rfl)
    exact bl_euclidean_H1 Riesz1.Externals.prekopa_leindler_proof
      (scalarPoincare_radial_dimension hN) (bounded_scalarPoincareRadialDomain basis)
      (isOpen_scalarPoincareRadialDomain basis) (nonempty_scalarPoincareRadialDomain basis)
      (convex_scalarPoincareRadialDomain basis)
      ((contDiffOn_scalarPoincareRadialPotential basis χ).of_le (by norm_num))
      (by positivity) (fun _ hq u => hessian_scalarPoincareRadialPotential_lower basis χ hq u) hfg
  have hle := integral_mono_ae (integrable_const (μ := η) (∫ q, (f q - ∫ r, f r ∂ν) ^ 2 ∂ν))
    hQ.integral_prod_right hsbound
  rw [integral_const, probReal_univ, smul_eq_mul, one_mul, ← integral_prod_symm Q hQ] at hle
  dsimp only
  change (∫ p, (F p - ∫ r, F r ∂ν.prod η) ^ 2 ∂ν.prod η) ≤ _
  rw [integral_congr_ae hrep]
  have hm : (∫ p, f p.1 ∂ν.prod η) = ∫ q, f q ∂ν := by
    rw [integral_fun_fst, probReal_univ, one_smul]
  rw [hm, integral_congr_ae (hrep.mono fun _ hp => congrArg (fun a => (a - ∫ q, f q ∂ν) ^ 2) hp)]
  rw [integral_fun_fst (μ := ν) (ν := η) (fun q => (f q - ∫ r, f r ∂ν) ^ 2),
    probReal_univ, one_smul]
  exact hle

/-- Brascamp–Lieb for every rotation invariant element of the Gibbs Sobolev space.
The inverse acts on the mean zero hyperplane. The inverse Hessian energy is integrable. -/
theorem brascamp_lieb_circle (hN : 2 ≤ (N : ℕ))
    (χ : HsPairPotentials N c) (hc : 0 < c)
    (f : HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)))
    (hinv : let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
      ∀ t : ℝ, (fun x => hsSobolevValue μ f (hsGapRotate t x)) =ᵐ[μ]
        (hsSobolevValue μ f : HsConfiguration N → ℝ)) :
    let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
    Integrable (fun x => inner ℝ (hsSobolevGradient μ f x)
      (blCircleInverseHessian χ hc x (hsSobolevGradient μ f x))) μ ∧
    (∫ x, (hsSobolevValue μ f x - ∫ y, hsSobolevValue μ f y ∂μ) ^ 2 ∂μ) ≤
      ∫ x, inner ℝ (hsSobolevGradient μ f x)
        (blCircleInverseHessian χ hc x (hsSobolevGradient μ f x)) ∂μ := by
  let basis := stdOrthonormalBasis ℝ (hsOrthSubspace N)
  let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
  let ν := (volume.restrict (scalarPoincareRadialDomain basis)).tilted
    (fun q => -scalarPoincareRadialPotential basis χ q)
  let ρ := ν.prod (AddCircle.haarAddCircle : Measure (AddCircle (Real.sqrt (N : ℕ))))
  let C := blockQuotientProductCoord basis
  have hC : MeasurableEmbedding C := measurableEmbedding_blockQuotientProductCoord basis
  have hmap : μ.map C = ρ := blCircle_coord_map basis χ hc
  have hgraph := (hsSobolev_iff_graph μ (hsSobolevValue μ f) (hsSobolevGradient μ f)
    (Lp.memLp _) (Lp.memLp _)).mp (by
      simp only [Lp.toLp_coeFn]
      change WithLp.toLp 2 ((WithLp.ofLp f.val).1, (WithLp.ofLp f.val).2) ∈ hsSobolevSubmodule μ
      simpa only [Prod.mk.eta, WithLp.toLp_ofLp] using f.property)
  obtain ⟨F, G, hprod, heF, heG⟩ := block_quotient_graph_transport basis hgraph
  change ∀ x, F (C x) = hsSobolevValue μ f x at heF
  change ∀ x, G (C x) = hsSobolevGradient μ f x at heG
  change WeightedSobolev.IsGraphH1 (μ.map C) _ _ _ F G at hprod
  rw [hmap] at hprod
  obtain ⟨g, _, hg⟩ := (hsLp_gap_factorization_iff_rotation χ hc (hsSobolevValue μ f)).mpr hinv
  let fr := fun q => g (hsGap (scalarPoincareRadialEmbedding basis q))
  have hrep : F =ᵐ[ρ] (fun p => fr p.1) := by
    rw [← hmap]
    apply hC.ae_map_iff.mpr
    filter_upwards [hg] with x hx
    rw [heF, hx]
    dsimp only [fr, C]
    rw [blCircle_coord_radial, hsOrthProj_eq_translate, hsGap_translate]
  let Q := fun p => sSup (Set.range fun u =>
    2 * inner ℝ (blockRadialGradientMap basis (G p)) u -
      fderiv ℝ (fderiv ℝ (scalarPoincareRadialPotential basis χ)) p.1 u u)
  have heQ (x : HsConfiguration N) :
      Q (C x) = blCircleEnergy χ x (hsSobolevGradient μ f x) := by
    dsimp only [Q, C]
    rw [heG]
    exact blCircle_coord_energy basis χ x _
  have hQi : Integrable Q ρ := by
    rw [← hmap, hC.integrable_map_iff]
    simpa only [Function.comp_def, heQ] using
      blCircleEnergy_integrable χ hc (hsSobolevGradient μ f) (Lp.memLp _)
  have hbound := blCircle_product_bound basis hN χ hc hprod hrep hQi
  have hmean : (∫ p, F p ∂ρ) = ∫ x, hsSobolevValue μ f x ∂μ := by
    rw [← hmap, hC.integral_map]
    simp only [heF]
  change (∫ p, (F p - ∫ r, F r ∂ρ) ^ 2 ∂ρ) ≤ ∫ p, Q p ∂ρ at hbound
  rw [hmean, ← hmap, hC.integral_map, hC.integral_map] at hbound
  simp only [heF, heQ, blCircleEnergy_eq_inverse χ hc] at hbound
  refine ⟨?_, hbound⟩
  simpa only [blCircleEnergy_eq_inverse χ hc] using
    blCircleEnergy_integrable χ hc (hsSobolevGradient μ f) (Lp.memLp _)

end Riesz1

end
