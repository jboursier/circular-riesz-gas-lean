/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.BlockConcentrationCurvature
public import Riesz1.HelfferSjostrand.ConvexityExteriorDensity
public import Riesz1.HelfferSjostrand.GeometryLawProduct
public import Riesz1.HelfferSjostrand.ScalarPoincareRadialLaw

/-!
# Product coordinates for circular block marginals

The measure identification in Lemma 3.9. The exterior contribution is
only convex and translation invariant. It need not be a smooth pair Hamiltonian.
The coordinate factorization is consequently proved for arbitrary measurable radial weights.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Riesz1

/-- Orthogonal coordinates send fundamental-region volume to radial volume times
arclength on the rotation circle, including the one-particle case. -/
theorem block_volume_map_hsCoord (M : ℕ+) :
    (volume.restrict (hsFundamentalRegion M)).map (hsCoord M) =
      (volume.restrict (hsRadialDomain M)).prod
        (volume : Measure (AddCircle (Real.sqrt (M : ℕ)))) := by
  symm
  apply Measure.prod_eq
  intro s t hs ht
  rw [Measure.map_apply (measurable_hsCoord M) (hs.prod ht),
    ← lintegral_indicator_fun_one ((hs.prod ht).preimage (measurable_hsCoord M))]
  have hp : ∀ x : HsEuclidean M,
      (hsCoord M ⁻¹' (s ×ˢ t)).indicator (fun _ => (1 : ℝ≥0∞)) x =
        s.indicator (fun _ => (1 : ℝ≥0∞)) (hsOrthComp M x) *
          t.indicator (fun _ => (1 : ℝ≥0∞)) (hsAngle M x) := by
    intro x
    by_cases hx : hsOrthComp M x ∈ s <;> by_cases hy : hsAngle M x ∈ t <;>
      simp [hsCoord, hx, hy]
  rw [lintegral_congr hp,
    lintegral_hsFundamentalRegion_fiber M (measurable_const.indicator hs)
      (measurable_const.indicator ht),
    lintegral_indicator_const hs, lintegral_indicator_const ht, one_mul, one_mul]

/-- Measurable radial weights preserve the volume product decomposition. No smoothness
or finite normalization of the weight is required. -/
theorem block_radialWeight_map_hsCoord (M : ℕ+)
    {w : hsOrthSubspace M → ℝ≥0∞} (hw : Measurable w) :
    ((volume.restrict (hsFundamentalRegion M)).withDensity
      (fun x => w (hsOrthComp M x))).map (hsCoord M) =
      ((volume.restrict (hsRadialDomain M)).withDensity w).prod
        (volume : Measure (AddCircle (Real.sqrt (M : ℕ)))) := by
  rw [prod_withDensity_left hw, ← block_volume_map_hsCoord]
  apply Measure.ext_of_lintegral
  intro f hf
  have hw' : Measurable (fun z : hsOrthSubspace M × AddCircle (Real.sqrt (M : ℕ)) =>
      w z.1) := hw.comp measurable_fst
  rw [lintegral_map hf (measurable_hsCoord M)]
  rw [lintegral_withDensity_eq_lintegral_mul _
    (f := fun x => w (hsOrthComp M x)) (hw.comp (measurable_hsOrthComp M))
    (g := fun x => f (hsCoord M x)) (hf.comp (measurable_hsCoord M))]
  rw [lintegral_withDensity_eq_lintegral_mul _ hw' hf]
  simp only [Pi.mul_apply]
  rw [lintegral_map (f := fun z => w z.1 * f z) (hw'.mul hf) (measurable_hsCoord M)]
  rfl

variable {N M : ℕ+} {c : ℝ} {n : ℕ}

/-- The actual marginal potential is invariant under orthogonal projection. -/
theorem blockPotential_orthComp (χ : HsPairPotentials N c)
    (e : Fin (M : ℕ) ⊕ Fin n ≃ Fin (N : ℕ))
    (hmono : StrictMono fun a => e (Sum.inl a)) (x : HsEuclidean M)
    (_hx : x ∈ hsChamber M) :
    blockRetainedEnergy χ e (hsOrthComp M x) + blockTilde χ e (hsOrthComp M x) =
      blockRetainedEnergy χ e x + blockTilde χ e x := by
  have h1 : blockRetainedEnergy χ e (hsOrthComp M x) = blockRetainedEnergy χ e x := by
    rw [blockRetainedEnergy_eq_pairExpression χ e hmono]
    exact hsPairExpression_orthProj (blockPairPotentials χ e hmono) x
  have ht : (hsOrthComp M x : HsEuclidean M) = x + constVec (M : ℕ)
      (-(inner ℝ x (hsUnitVector M) / Real.sqrt (M : ℕ))) := by
    change hsOrthProj M x = _
    rw [hsOrthProj_eq_translate]
    ext i
    simp only [hsTranslate_apply, PiLp.add_apply, constVec_apply]
  rw [h1, ht, blockTilde_translate]

/-- The Gibbs block potential is continuous on its chamber, even when the exterior
potential has no classical Hessian. -/
theorem continuousOn_blockPotential (hPL : External.PrekopaLeindler)
    (χ : HsPairPotentials N c) (hc : 0 < c)
    (e : Fin (M : ℕ) ⊕ Fin n ≃ Fin (N : ℕ))
    (hmono : StrictMono fun a => e (Sum.inl a))
    (he0 : e (Sum.inl ⟨0, M.pos⟩) = ⟨0, N.pos⟩) :
    ContinuousOn (fun x => blockRetainedEnergy χ e x + blockTilde χ e x) (hsChamber M) := by
  have ht := (convexOn_blockTilde hPL χ hc e hmono M.pos he0).continuousOn_interior
  rw [(isOpen_retainedChamber (M : ℕ)).interior_eq, retainedChamber_eq_hsChamber] at ht
  rw [blockRetainedEnergy_eq_pairExpression χ e hmono]
  exact (hsPairExpression_contDiffOn (blockPairPotentials χ e hmono)).continuousOn.add ht

/-- The marginal density on the whole lift space, zero outside its chamber. -/
def blockMarginalDensity (χ : HsPairPotentials N c)
    (e : Fin (M : ℕ) ⊕ Fin n ≃ Fin (N : ℕ)) (x : HsEuclidean M) : ℝ≥0∞ :=
  (hsChamber M).indicator (fun x => ENNReal.ofReal
    (Real.exp (-(blockRetainedEnergy χ e x + blockTilde χ e x)))) x

theorem measurable_blockMarginalDensity (hPL : External.PrekopaLeindler)
    (χ : HsPairPotentials N c) (hc : 0 < c)
    (e : Fin (M : ℕ) ⊕ Fin n ≃ Fin (N : ℕ))
    (hmono : StrictMono fun a => e (Sum.inl a))
    (he0 : e (Sum.inl ⟨0, M.pos⟩) = ⟨0, N.pos⟩) :
    Measurable (blockMarginalDensity χ e) := by
  classical
  have hcont := ENNReal.continuous_ofReal.comp_continuousOn
    (Real.continuous_exp.comp_continuousOn
      (continuousOn_blockPotential hPL χ hc e hmono he0).neg)
  unfold blockMarginalDensity
  rw [← piecewise_eq_indicator]
  exact ContinuousOn.measurable_piecewise hcont continuousOn_const
    (isOpen_hsChamber M).measurableSet

theorem blockMarginalDensity_orthComp (χ : HsPairPotentials N c)
    (e : Fin (M : ℕ) ⊕ Fin n ≃ Fin (N : ℕ))
    (hmono : StrictMono fun a => e (Sum.inl a)) (x : HsEuclidean M) :
    blockMarginalDensity χ e (hsOrthComp M x) = blockMarginalDensity χ e x := by
  have hm : (hsOrthComp M x : HsEuclidean M) ∈ hsChamber M ↔ x ∈ hsChamber M := by
    change hsOrthProj M x ∈ hsChamber M ↔ _
    rw [hsOrthProj_eq_translate]
    exact hsTranslate_mem_chamber_iff _ _
  by_cases hx : x ∈ hsChamber M
  · rw [blockMarginalDensity, indicator_of_mem (hm.mpr hx),
      blockPotential_orthComp χ e hmono x hx, blockMarginalDensity, indicator_of_mem hx]
  · rw [blockMarginalDensity, indicator_of_notMem (fun h => hx (hm.mp h)),
      blockMarginalDensity, indicator_of_notMem hx]

/-- The lift marginal as an equality of measures, with its normalization inherited
from the original Gibbs probability. -/
theorem hsGibbs_map_retainedCoord (hPL : External.PrekopaLeindler)
    (χ : HsPairPotentials N c) (hc : 0 < c)
    (e : Fin (M : ℕ) ⊕ Fin n ≃ Fin (N : ℕ))
    (hmono : StrictMono fun a => e (Sum.inl a))
    (he0 : e (Sum.inl ⟨0, M.pos⟩) = ⟨0, N.pos⟩) :
    (hsGibbsProbability χ hc : Measure (Configuration N)).map (retainedCoord e) =
      (hsPartitionFunction χ)⁻¹ •
        (volume.restrict (hsFundamentalRegion M)).withDensity (blockMarginalDensity χ e) := by
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map hg (blockDensity_continuous_retainedCoord e).measurable,
    hsGibbs_retainedCoord_lintegral χ hc e hmono M.pos he0 hPL g hg,
    lintegral_smul_measure, smul_eq_mul,
    lintegral_withDensity_eq_lintegral_mul _
      (measurable_blockMarginalDensity hPL χ hc e hmono he0) hg]
  congr 1
  have hregion : retainedChamber (M : ℕ) ∩
      {z : HsEuclidean M | 0 ≤ z ⟨0, M.pos⟩ ∧ z ⟨0, M.pos⟩ < 1} =
      hsFundamentalRegion M := by
    rw [retainedChamber_eq_hsChamber]
    rfl
  rw [hregion]
  apply setLIntegral_congr_fun (measurableSet_hsFundamentalRegion M)
  intro x hx
  rw [Pi.mul_apply, blockMarginalDensity, indicator_of_mem hx.1, mul_comm]

/-- The unnormalized radial measure for a retained block. -/
def blockRadialMeasure (χ : HsPairPotentials N c)
    (e : Fin (M : ℕ) ⊕ Fin n ≃ Fin (N : ℕ)) : Measure (hsOrthSubspace M) :=
  (volume.restrict (hsRadialDomain M)).withDensity
    (fun z => blockMarginalDensity χ e (z : HsEuclidean M))

/-- Product coordinates for the actual retained marginal. The circle factor is arclength.
The normalization is the partition function of the full Gibbs law. -/
theorem hsGibbs_map_blockCoord (hPL : External.PrekopaLeindler)
    (χ : HsPairPotentials N c) (hc : 0 < c)
    (e : Fin (M : ℕ) ⊕ Fin n ≃ Fin (N : ℕ))
    (hmono : StrictMono fun a => e (Sum.inl a))
    (he0 : e (Sum.inl ⟨0, M.pos⟩) = ⟨0, N.pos⟩) :
    (hsGibbsProbability χ hc : Measure (Configuration N)).map
      (fun X => hsCoord M (retainedCoord e X)) =
      (hsPartitionFunction χ)⁻¹ • (blockRadialMeasure χ e).prod
        (volume : Measure (AddCircle (Real.sqrt (M : ℕ)))) := by
  change (hsGibbsProbability χ hc : Measure (Configuration N)).map
    (hsCoord M ∘ retainedCoord e) = _
  rw [← Measure.map_map (measurable_hsCoord M)
      (blockDensity_continuous_retainedCoord e).measurable,
    hsGibbs_map_retainedCoord hPL χ hc e hmono he0,
    Measure.map_smul (hsPartitionFunction χ)⁻¹ (measurable_hsCoord M).aemeasurable]
  apply congrArg (fun μ : Measure (hsOrthSubspace M × AddCircle (Real.sqrt (M : ℕ))) =>
    (hsPartitionFunction χ)⁻¹ • μ)
  have hw : Measurable (fun z : hsOrthSubspace M =>
      blockMarginalDensity χ e (z : HsEuclidean M)) :=
    (measurable_blockMarginalDensity hPL χ hc e hmono he0).comp measurable_subtype_coe
  have heq : blockMarginalDensity χ e =
      fun x => blockMarginalDensity χ e (hsOrthComp M x) :=
    funext fun x => (blockMarginalDensity_orthComp χ e hmono x).symm
  have hwmap := block_radialWeight_map_hsCoord M
    (w := fun z => blockMarginalDensity χ e (z : HsEuclidean M)) hw
  have hdmap := congrArg (fun ρ : HsEuclidean M → ℝ≥0∞ =>
    ((volume.restrict (hsFundamentalRegion M)).withDensity ρ).map (hsCoord M)) heq
  exact hdmap.trans hwmap

/-- The full partition function is the radial block mass times the rotation length. -/
theorem hsPartitionFunction_eq_blockRadial (hPL : External.PrekopaLeindler)
    (χ : HsPairPotentials N c) (hc : 0 < c)
    (e : Fin (M : ℕ) ⊕ Fin n ≃ Fin (N : ℕ))
    (hmono : StrictMono fun a => e (Sum.inl a))
    (he0 : e (Sum.inl ⟨0, M.pos⟩) = ⟨0, N.pos⟩) :
    hsPartitionFunction χ = blockRadialMeasure χ e univ *
      ENNReal.ofReal (Real.sqrt (M : ℕ)) := by
  have h := congrArg (fun μ : Measure (hsOrthSubspace M ×
    AddCircle (Real.sqrt (M : ℕ))) => μ univ)
    (hsGibbs_map_blockCoord hPL χ hc e hmono he0)
  rw [Measure.map_apply (show Measurable (fun X => hsCoord M (retainedCoord e X)) from
      (measurable_hsCoord M).comp
        (blockDensity_continuous_retainedCoord e).measurable) MeasurableSet.univ,
    preimage_univ, measure_univ, Measure.smul_apply, smul_eq_mul,
    ← univ_prod_univ, Measure.prod_prod, AddCircle.measure_univ] at h
  calc
    hsPartitionFunction χ = hsPartitionFunction χ * 1 := (mul_one _).symm
    _ = hsPartitionFunction χ * ((hsPartitionFunction χ)⁻¹ *
        (blockRadialMeasure χ e univ * ENNReal.ofReal (Real.sqrt (M : ℕ)))) := by rw [← h]
    _ = _ := by
      rw [← mul_assoc, ENNReal.mul_inv_cancel (hsPartitionFunction_pos χ).ne'
        (hsPartitionFunction_lt_top χ hc).ne, one_mul]

theorem blockRadialMeasure_univ_ne_zero (hPL : External.PrekopaLeindler)
    (χ : HsPairPotentials N c) (hc : 0 < c)
    (e : Fin (M : ℕ) ⊕ Fin n ≃ Fin (N : ℕ))
    (hmono : StrictMono fun a => e (Sum.inl a))
    (he0 : e (Sum.inl ⟨0, M.pos⟩) = ⟨0, N.pos⟩) :
    blockRadialMeasure χ e univ ≠ 0 := by
  intro hz
  have h := hsPartitionFunction_eq_blockRadial hPL χ hc e hmono he0
  rw [hz, zero_mul] at h
  exact (hsPartitionFunction_pos χ).ne' h

theorem blockRadialMeasure_univ_ne_top (hPL : External.PrekopaLeindler)
    (χ : HsPairPotentials N c) (hc : 0 < c)
    (e : Fin (M : ℕ) ⊕ Fin n ≃ Fin (N : ℕ))
    (hmono : StrictMono fun a => e (Sum.inl a))
    (he0 : e (Sum.inl ⟨0, M.pos⟩) = ⟨0, N.pos⟩) :
    blockRadialMeasure χ e univ ≠ ⊤ := by
  intro hz
  have h := hsPartitionFunction_eq_blockRadial hPL χ hc e hmono he0
  rw [hz, ENNReal.top_mul (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr M.pos))).ne'] at h
  exact (hsPartitionFunction_lt_top χ hc).ne h

/-- The normalized radial factor of the retained marginal. -/
def blockRadialProbability (hPL : External.PrekopaLeindler)
    (χ : HsPairPotentials N c) (hc : 0 < c)
    (e : Fin (M : ℕ) ⊕ Fin n ≃ Fin (N : ℕ))
    (hmono : StrictMono fun a => e (Sum.inl a))
    (he0 : e (Sum.inl ⟨0, M.pos⟩) = ⟨0, N.pos⟩) : ProbabilityMeasure (hsOrthSubspace M) :=
  ⟨(blockRadialMeasure χ e univ)⁻¹ • blockRadialMeasure χ e, by
    rw [isProbabilityMeasure_iff, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (blockRadialMeasure_univ_ne_zero hPL χ hc e hmono he0)
      (blockRadialMeasure_univ_ne_top hPL χ hc e hmono he0)⟩

/-- The retained circular marginal factors as its radial probability and uniform rotation.
This is the product-law step of Lemma 3.9, for every nonempty increasing block
containing label zero, including a singleton. -/
theorem hsGibbs_map_blockCoord_probability (hPL : External.PrekopaLeindler)
    (χ : HsPairPotentials N c) (hc : 0 < c)
    (e : Fin (M : ℕ) ⊕ Fin n ≃ Fin (N : ℕ))
    (hmono : StrictMono fun a => e (Sum.inl a))
    (he0 : e (Sum.inl ⟨0, M.pos⟩) = ⟨0, N.pos⟩) :
    (hsGibbsProbability χ hc : Measure (Configuration N)).map
      (fun X => hsCoord M (retainedCoord e X)) =
      (blockRadialProbability hPL χ hc e hmono he0 : Measure _).prod
        (hsUniformCircle M : Measure _) := by
  rw [hsGibbs_map_blockCoord hPL χ hc e hmono he0,
    hsPartitionFunction_eq_blockRadial hPL χ hc e hmono he0, volume_eq_hsUniformCircle]
  change _ = ((blockRadialMeasure χ e univ)⁻¹ • blockRadialMeasure χ e).prod _
  rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  congr 1
  have hm0 := blockRadialMeasure_univ_ne_zero hPL χ hc e hmono he0
  have hmt := blockRadialMeasure_univ_ne_top hPL χ hc e hmono he0
  rw [ENNReal.mul_inv (Or.inl hm0) (Or.inl hmt), mul_assoc,
    ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr M.pos))).ne'
      ENNReal.ofReal_ne_top, mul_one]

/-- On its support the radial block measure has exactly the density `exp (−H₁−H̃)`. -/
theorem blockRadialMeasure_eq (χ : HsPairPotentials N c)
    (e : Fin (M : ℕ) ⊕ Fin n ≃ Fin (N : ℕ)) :
    blockRadialMeasure χ e = (volume.restrict (hsRadialDomain M)).withDensity
      (fun z => ENNReal.ofReal (Real.exp
        (-(blockRetainedEnergy χ e (z : HsEuclidean M) + blockTilde χ e z)))) := by
  unfold blockRadialMeasure
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem (measurableSet_hsRadialDomain M)] with z hz
  exact indicator_of_mem (show (z : HsEuclidean M) ∈ hsChamber M from hz)
    (fun x => ENNReal.ofReal (Real.exp (-(blockRetainedEnergy χ e x + blockTilde χ e x))))

/-- The normalized radial marginal is the exponential tilt used in the radial Herbst bound. -/
theorem blockRadialProbability_eq_tilted (hPL : External.PrekopaLeindler)
    (χ : HsPairPotentials N c) (hc : 0 < c)
    (e : Fin (M : ℕ) ⊕ Fin n ≃ Fin (N : ℕ))
    (hmono : StrictMono fun a => e (Sum.inl a))
    (he0 : e (Sum.inl ⟨0, M.pos⟩) = ⟨0, N.pos⟩) :
    (blockRadialProbability hPL χ hc e hmono he0 : Measure _) =
      (volume.restrict (hsRadialDomain M)).tilted
        (fun z => -(blockRetainedEnergy χ e (z : HsEuclidean M) + blockTilde χ e z)) := by
  let W : hsOrthSubspace M → ℝ := fun z => Real.exp
    (-(blockRetainedEnergy χ e (z : HsEuclidean M) + blockTilde χ e z))
  have hmass : blockRadialMeasure χ e univ =
      ∫⁻ z in hsRadialDomain M, ENNReal.ofReal (W z) := by
    rw [blockRadialMeasure_eq, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hWc : ContinuousOn W (hsRadialDomain M) :=
    Real.continuous_exp.comp_continuousOn
      (((continuousOn_blockPotential hPL χ hc e hmono he0).comp
        continuous_subtype_val.continuousOn (fun _ hz => hz)).neg)
  have hW : IntegrableOn W (hsRadialDomain M) :=
    (lintegral_ofReal_ne_top_iff_integrable
      (hWc.aestronglyMeasurable (measurableSet_hsRadialDomain M))
      (Filter.Eventually.of_forall fun z => (Real.exp_pos _).le)).mp
        (hmass ▸ blockRadialMeasure_univ_ne_top hPL χ hc e hmono he0)
  have hZ : 0 < ∫ z in hsRadialDomain M, W z := by
    have he := ofReal_integral_eq_lintegral_ofReal hW
      (Filter.Eventually.of_forall fun z => (Real.exp_pos _).le)
    rw [← hmass] at he
    exact ENNReal.ofReal_pos.mp (he.symm ▸ bot_lt_iff_ne_bot.mpr
      (blockRadialMeasure_univ_ne_zero hPL χ hc e hmono he0))
  rw [poincare_tilted_eq_normalized _ _ hW hZ]
  change (blockRadialMeasure χ e univ)⁻¹ • blockRadialMeasure χ e = _
  rw [← hmass, blockRadialMeasure_eq]

/-- Orthonormal coordinates transport the radial tilt in part 1 of Lemma 3.9
to the actual radial factor of the retained marginal. -/
theorem blockRadialChart_map (hPL : External.PrekopaLeindler)
    (χ : HsPairPotentials N c) (hc : 0 < c)
    (e : Fin (M : ℕ) ⊕ Fin n ≃ Fin (N : ℕ))
    (hmono : StrictMono fun a => e (Sum.inl a))
    (he0 : e (Sum.inl ⟨0, M.pos⟩) = ⟨0, N.pos⟩)
    (basis : OrthonormalBasis (Fin (Module.finrank ℝ (hsOrthSubspace M))) ℝ
      (hsOrthSubspace M)) :
    (((volume.restrict (scalarPoincareRadialDomain basis)).tilted
      (fun q => -(blockRetainedEnergy χ e (scalarPoincareRadialEmbedding basis q) +
        blockTilde χ e (scalarPoincareRadialEmbedding basis q)))).map
        (scalarPoincareRadialChart basis)) =
      (blockRadialProbability hPL χ hc e hmono he0 : Measure _) := by
  rw [blockRadialProbability_eq_tilted hPL χ hc e hmono he0]
  exact poincare_isometry_tilted (scalarPoincareRadialChart basis)
    ((isOpen_hsChamber M).preimage continuous_subtype_val)
    (fun z => -(blockRetainedEnergy χ e (z : HsEuclidean M) + blockTilde χ e z))

/-- The original Gibbs law sends the retained orthogonal coordinate to the radial
block probability. -/
theorem hsGibbs_blockRadial_measurePreserving (hPL : External.PrekopaLeindler)
    (χ : HsPairPotentials N c) (hc : 0 < c)
    (e : Fin (M : ℕ) ⊕ Fin n ≃ Fin (N : ℕ))
    (hmono : StrictMono fun a => e (Sum.inl a))
    (he0 : e (Sum.inl ⟨0, M.pos⟩) = ⟨0, N.pos⟩) :
    MeasurePreserving (fun X => hsOrthComp M (retainedCoord e X))
      (hsGibbsProbability χ hc : Measure (Configuration N))
      (blockRadialProbability hPL χ hc e hmono he0 : Measure _) := by
  have hm : Measurable (fun X => hsCoord M (retainedCoord e X)) :=
    (measurable_hsCoord M).comp (blockDensity_continuous_retainedCoord e).measurable
  have h := congrArg (fun μ : Measure (hsOrthSubspace M × AddCircle (Real.sqrt (M : ℕ))) =>
    μ.map Prod.fst) (hsGibbs_map_blockCoord_probability hPL χ hc e hmono he0)
  rw [Measure.map_map measurable_fst hm, Measure.map_fst_prod, measure_univ, one_smul] at h
  exact ⟨(measurable_hsOrthComp M).comp
    (blockDensity_continuous_retainedCoord e).measurable, h⟩

/-- Expectations of every measurable radial observable agree with the original Gibbs
expectations. This applies both to a radial Sobolev observable and to its exponential. -/
theorem hsGibbs_blockRadial_integral (hPL : External.PrekopaLeindler)
    (χ : HsPairPotentials N c) (hc : 0 < c)
    (e : Fin (M : ℕ) ⊕ Fin n ≃ Fin (N : ℕ))
    (hmono : StrictMono fun a => e (Sum.inl a))
    (he0 : e (Sum.inl ⟨0, M.pos⟩) = ⟨0, N.pos⟩)
    {F : hsOrthSubspace M → ℝ}
    (hF : AEStronglyMeasurable F (blockRadialProbability hPL χ hc e hmono he0 : Measure _)) :
    (∫ X, F (hsOrthComp M (retainedCoord e X)) ∂(hsGibbsProbability χ hc : Measure _)) =
      ∫ z, F z ∂(blockRadialProbability hPL χ hc e hmono he0 : Measure _) := by
  have hp := hsGibbs_blockRadial_measurePreserving hPL χ hc e hmono he0
  rw [← hp.map_eq] at hF ⊢
  exact (integral_map hp.measurable.aemeasurable hF).symm

end Riesz1

end
