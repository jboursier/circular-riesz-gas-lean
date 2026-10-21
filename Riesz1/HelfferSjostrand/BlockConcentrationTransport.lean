/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.BlockConcentrationDescent
public import Riesz1.HelfferSjostrand.BlockConcentrationProduct
public import Riesz1.HelfferSjostrand.BlockConcentrationRadial

/-!
# Transport of marginal Sobolev jets to product coordinates

The measurable coordinate map is an embedding, so the defining smooth graph on the
quotient pushes forward to the periodic product graph. The normalized block law is
transported into the same orthonormal radial chart. This is a step of Lemma 3.9.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set

namespace Riesz1

variable {M N : ℕ+} {n : ℕ} {c : ℝ}

/-- Orthogonal product coordinates of a point of the configuration quotient. -/
def blockQuotientProductCoord
    (basis : OrthonormalBasis (Fin (Module.finrank ℝ (hsOrthSubspace M))) ℝ (hsOrthSubspace M))
    (x : HsConfiguration M) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ (hsOrthSubspace M))) ×
      AddCircle (Real.sqrt (M : ℕ)) :=
  ((scalarPoincareRadialChart basis).symm
    (hsConfigCoord M ((hsConfigurationEquiv M).symm x)).1,
    (hsConfigCoord M ((hsConfigurationEquiv M).symm x)).2)

theorem measurableEmbedding_blockQuotientProductCoord
    (basis : OrthonormalBasis (Fin (Module.finrank ℝ (hsOrthSubspace M))) ℝ (hsOrthSubspace M)) :
    MeasurableEmbedding (blockQuotientProductCoord basis) := by
  let C := fun X : Configuration M =>
    ((scalarPoincareRadialChart basis).symm (hsConfigCoord M X).1, (hsConfigCoord M X).2)
  have hm : Measurable C :=
    ((scalarPoincareRadialChart basis).symm.continuous.measurable.comp
      (measurable_fst.comp (measurable_hsConfigCoord M))).prodMk
        (measurable_snd.comp (measurable_hsConfigCoord M))
  have hi : Function.Injective C := by
    intro X Y h
    apply (hsConfigCoord_bijOn M).injOn (mem_univ _) (mem_univ _)
    apply Prod.ext
    · exact (scalarPoincareRadialChart basis).symm.injective (congrArg Prod.fst h)
    · change (C X).2 = (C Y).2
      exact congrArg Prod.snd h
  let : StandardBorelSpace (Configuration M) := (measurableSet_orderedDomain M).standardBorel
  exact (hm.measurableEmbedding hi).comp
    (hsConfigurationMeasurableEquiv M).symm.measurableEmbedding

/-- The quotient Sobolev graph transports to the actual product smooth graph. -/
theorem block_quotient_graph_transport
    (basis : OrthonormalBasis (Fin (Module.finrank ℝ (hsOrthSubspace M))) ℝ (hsOrthSubspace M))
    {μ : Measure (HsConfiguration M)} {F : HsConfiguration M → ℝ}
    {G : HsConfiguration M → HsEuclidean M}
    (hFG : WeightedSobolev.IsGraphH1 μ (fun _ : hsSmoothCore M => True)
      (fun f => hsSmoothValue f.val) hsSmoothGradient F G) :
    ∃ F' G', WeightedSobolev.IsGraphH1 (μ.map (blockQuotientProductCoord basis))
      (fun _ : hsSmoothCore M => True)
      (fun f => scalarPoincareProductExtension basis f.val)
      (fun f => scalarPoincareProductExtension basis (gradient f.val)) F' G' ∧
      (∀ x, F' (blockQuotientProductCoord basis x) = F x) ∧
      (∀ x, G' (blockQuotientProductCoord basis x) = G x) := by
  apply hFG.exists_map (measurableEmbedding_blockQuotientProductCoord basis)
  · intro f _ x
    exact scalarPoincareProductExtension_config basis f.val f.property.1
      ((hsConfigurationEquiv M).symm x)
  · intro f _ x
    exact scalarPoincareProductExtension_config basis (gradient f.val)
      (scalarPoincare_gradient_translate f.property) ((hsConfigurationEquiv M).symm x)

/-- The ordered retained coordinates, when the first label is retained, are already
in the fundamental region. -/
def blockRetainedConfiguration (e : Fin (M : ℕ) ⊕ Fin n ≃ Fin (N : ℕ))
    (hmono : StrictMono fun a => e (Sum.inl a))
    (he0 : e (Sum.inl ⟨0, M.pos⟩) = ⟨0, N.pos⟩) (X : Configuration N) : Configuration M :=
  ⟨fun a => X.val (e (Sum.inl a)), by
    refine ⟨X.property.1.comp hmono, ?_, ?_, ?_⟩
    · simpa only [he0] using X.property.2.1
    · simpa only [he0] using X.property.2.2.1
    · intro i
      simpa only [he0] using X.property.2.2.2 (e (Sum.inl i))⟩

/-- Projection to the retained configuration quotient. -/
def blockQuotientProjection (e : Fin (M : ℕ) ⊕ Fin n ≃ Fin (N : ℕ))
    (hmono : StrictMono fun a => e (Sum.inl a))
    (he0 : e (Sum.inl ⟨0, M.pos⟩) = ⟨0, N.pos⟩) (X : Configuration N) : HsConfiguration M :=
  hsConfigurationMap M (blockRetainedConfiguration e hmono he0 X)

theorem measurable_blockQuotientProjection (e : Fin (M : ℕ) ⊕ Fin n ≃ Fin (N : ℕ))
    (hmono : StrictMono fun a => e (Sum.inl a))
    (he0 : e (Sum.inl ⟨0, M.pos⟩) = ⟨0, N.pos⟩) :
    Measurable (blockQuotientProjection e hmono he0) := by
  have hm : Measurable (fun X : Configuration N => fun a : Fin (M : ℕ) =>
      X.val (e (Sum.inl a))) := Measurable.of_eval fun a =>
    (measurable_pi_apply (e (Sum.inl a))).comp measurable_subtype_coe
  exact (measurable_hsConfigurationMap M).comp hm.subtype_mk

/-- The law of the retained configuration on its quotient manifold. -/
def blockQuotientMarginal (χ : HsPairPotentials N c) (hc : 0 < c)
    (e : Fin (M : ℕ) ⊕ Fin n ≃ Fin (N : ℕ))
    (hmono : StrictMono fun a => e (Sum.inl a))
    (he0 : e (Sum.inl ⟨0, M.pos⟩) = ⟨0, N.pos⟩) : ProbabilityMeasure (HsConfiguration M) :=
  (hsGibbsProbability χ hc).map (blockQuotientProjection e hmono he0)

/-- The marginal quotient law in orthonormal product coordinates. -/
theorem blockQuotientProjection_map_product (hPL : External.PrekopaLeindler)
    (χ : HsPairPotentials N c) (hc : 0 < c)
    (e : Fin (M : ℕ) ⊕ Fin n ≃ Fin (N : ℕ))
    (hmono : StrictMono fun a => e (Sum.inl a))
    (he0 : e (Sum.inl ⟨0, M.pos⟩) = ⟨0, N.pos⟩)
    (basis : OrthonormalBasis (Fin (Module.finrank ℝ (hsOrthSubspace M))) ℝ (hsOrthSubspace M)) :
    ((hsGibbsProbability χ hc : Measure (Configuration N)).map
      (blockQuotientProjection e hmono he0)).map (blockQuotientProductCoord basis) =
      ((volume.restrict (scalarPoincareRadialDomain basis)).tilted
        (fun q => -blockRadialPotential χ e basis q)).prod AddCircle.haarAddCircle := by
  let a := (scalarPoincareRadialChart basis).toHomeomorph.toMeasurableEquiv
  let ν := (volume.restrict (scalarPoincareRadialDomain basis)).tilted
    (fun q => -blockRadialPotential χ e basis q)
  have ha : (blockRadialProbability hPL χ hc e hmono he0 : Measure _).map a.symm = ν := by
    rw [← blockRadialChart_map hPL χ hc e hmono he0 basis]
    change (ν.map a).map a.symm = ν
    exact a.map_symm_map
  rw [Measure.map_map (measurableEmbedding_blockQuotientProductCoord basis).measurable
    (measurable_blockQuotientProjection e hmono he0)]
  have he : (blockQuotientProductCoord basis ∘ blockQuotientProjection e hmono he0) =
      (Prod.map a.symm id) ∘ (fun X => hsCoord M (retainedCoord e X)) := by
    funext X
    dsimp [blockQuotientProductCoord, blockQuotientProjection]
    change (_, _) = (_, _)
    rw [show (hsConfigurationEquiv M).symm
      (hsConfigurationMap M (blockRetainedConfiguration e hmono he0 X)) =
      blockRetainedConfiguration e hmono he0 X from (hsConfigurationEquiv M).symm_apply_apply _]
    rfl
  have hmC : Measurable (fun X : Configuration N => hsCoord M (retainedCoord e X)) :=
    (measurable_hsCoord M).comp (blockDensity_continuous_retainedCoord e).measurable
  rw [he, ← Measure.map_map (a.symm.measurable.prodMap measurable_id) hmC,
    hsGibbs_map_blockCoord_probability hPL χ hc e hmono he0,
    ← Measure.map_prod_map _ _ a.symm.measurable measurable_id, ha, Measure.map_id]
  rfl

end Riesz1

end
