/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.BlockConcentrationTransport

/-!
# The product-coordinate block Herbst bound

The analytic assembly of Lemma 3.9, before transporting the two
expectations back to the original Gibbs law.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set

namespace Riesz1.Internal

variable {N M : ℕ+} {n : ℕ} {c c₁ : ℝ}

/-- The full product graph, rather than a radial Sobolev certificate, is sufficient for
the sharp block Herbst estimate. Radial descent is a conclusion of the proof. -/
theorem block_product_concentration (hBE : External.BakryEmery)
    (hPL : External.PrekopaLeindler) (χ : HsPairPotentials N c) (hc : 0 < c) (hc₁ : 0 < c₁)
    (e : Fin (M : ℕ) ⊕ Fin n ≃ Fin (N : ℕ))
    (hmono : StrictMono fun a => e (Sum.inl a))
    (he0 : e (Sum.inl ⟨0, M.pos⟩) = ⟨0, N.pos⟩)
    (basis : OrthonormalBasis (Fin (Module.finrank ℝ (hsOrthSubspace M))) ℝ (hsOrthSubspace M))
    (hcurv : ∀ x ∈ hsChamber N, ∀ i j : Fin (M : ℕ), i < j → c₁ / 2 ≤
      deriv (deriv (χ.potential (e (Sum.inl i)) (e (Sum.inl j))))
        (x (e (Sum.inl j)) - x (e (Sum.inl i))))
    {F : EuclideanSpace ℝ (Fin (Module.finrank ℝ (hsOrthSubspace M))) ×
      AddCircle (Real.sqrt (M : ℕ)) → ℝ}
    {G : EuclideanSpace ℝ (Fin (Module.finrank ℝ (hsOrthSubspace M))) ×
      AddCircle (Real.sqrt (M : ℕ)) → HsEuclidean M}
    (hFG : WeightedSobolev.IsGraphH1
      (((volume.restrict (scalarPoincareRadialDomain basis)).tilted
        (fun q => -blockRadialPotential χ e basis q)).prod AddCircle.haarAddCircle)
      (fun _ : hsSmoothCore M => True) (fun f => scalarPoincareProductExtension basis f.val)
      (fun f => scalarPoincareProductExtension basis (gradient f.val)) F G)
    (hzero : ∀ᵐ p ∂(((volume.restrict (scalarPoincareRadialDomain basis)).tilted
      (fun q => -blockRadialPotential χ e basis q)).prod AddCircle.haarAddCircle),
      inner ℝ (G p) (hsUnitVector M) = 0)
    {L : ℝ} (hL : ∀ᵐ p ∂(((volume.restrict (scalarPoincareRadialDomain basis)).tilted
      (fun q => -blockRadialPotential χ e basis q)).prod AddCircle.haarAddCircle), ‖G p‖ ≤ L)
    (t : ℝ) :
    let ρ := ((volume.restrict (scalarPoincareRadialDomain basis)).tilted
      (fun q => -blockRadialPotential χ e basis q)).prod AddCircle.haarAddCircle
    Integrable F ρ ∧ Integrable (fun p => Real.exp (t * F p)) ρ ∧
      Real.log (∫ p, Real.exp (t * F p) ∂ρ) ≤
        t * (∫ p, F p ∂ρ) + t ^ 2 * L ^ 2 / (2 * c₁ * M) := by
  let ν := (volume.restrict (scalarPoincareRadialDomain basis)).tilted
    (fun q => -blockRadialPotential χ e basis q)
  have : IsProbabilityMeasure ν := by
    apply (Measure.isProbabilityMeasure_map_iff
      (scalarPoincareRadialChart basis).continuous.measurable.aemeasurable).mp
    rw [show ν.map (scalarPoincareRadialChart basis) =
      (blockRadialProbability hPL χ hc e hmono he0 : Measure _) from
        blockRadialChart_map hPL χ hc e hmono he0 basis]
    infer_instance
  have hν : ∀ᵐ q ∂ν, q ∈ scalarPoincareRadialDomain basis :=
    (withDensity_absolutelyContinuous _ _).ae_le
      (ae_restrict_mem (isOpen_scalarPoincareRadialDomain basis).measurableSet)
  obtain ⟨f, g, hfg, hgb, hrep⟩ := block_product_sobolev_descent basis ν hν hFG hzero hL
  obtain ⟨_, hfi, hei, hmgf⟩ :=
    block_radial_concentration hBE hPL χ hc hc₁ e hmono he0 basis hcurv hfg hgb t
  have hexp : (fun p => Real.exp (t * F p)) =ᵐ[ν.prod AddCircle.haarAddCircle]
      (fun p => Real.exp (t * f p.1)) := hrep.mono fun _ hp => congrArg (fun r => Real.exp (t * r)) hp
  refine ⟨(measurePreserving_fst.integrable_comp_of_integrable hfi).congr hrep.symm,
    (measurePreserving_fst.integrable_comp_of_integrable hei).congr hexp.symm, ?_⟩
  rw [integral_congr_ae hexp, integral_congr_ae hrep,
    integral_fun_fst (fun q => Real.exp (t * f q)), integral_fun_fst f]
  simpa only [probReal_univ, one_smul] using hmgf

end Riesz1.Internal

end
