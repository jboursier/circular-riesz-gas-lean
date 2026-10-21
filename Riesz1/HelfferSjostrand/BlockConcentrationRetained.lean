/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.BlockConcentrationProductHerbst
public import Riesz1.ToMathlib.MeasurePreservingIntegral

/-!
# Concentration for a retained block containing the first label

Lemma 3.9 for increasing retained labels containing label zero, including
singleton blocks. The original marginal Sobolev hypothesis is transported to product
coordinates and then descended to the radial law. The Bakry–Émery criterion
`External.BakryEmery` and the Prékopa–Leindler inequality `External.PrekopaLeindler` are passed
as extra hypotheses. Arbitrary cyclic relabelling is a separate packaging step.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set

namespace Riesz1

namespace Internal

variable {N M : ℕ+} {n : ℕ} {c c₁ : ℝ}

/-- Circular block concentration for any increasing retained set containing the first
label. Sobolev descent, exponential integrability and normalization are proved internally.
No admissibility or lower bound on the block size beyond nonemptiness is needed. -/
theorem block_marginal_concentration (hBE : External.BakryEmery)
    (hPL : External.PrekopaLeindler) (χ : HsPairPotentials N c) (hc : 0 < c) (hc₁ : 0 < c₁)
    (e : Fin (M : ℕ) ⊕ Fin n ≃ Fin (N : ℕ))
    (hmono : StrictMono fun a => e (Sum.inl a))
    (he0 : e (Sum.inl ⟨0, M.pos⟩) = ⟨0, N.pos⟩)
    (hcurv : ∀ x ∈ hsChamber N, ∀ i j : Fin (M : ℕ), i < j → c₁ / 2 ≤
      deriv (deriv (χ.potential (e (Sum.inl i)) (e (Sum.inl j))))
        (x (e (Sum.inl j)) - x (e (Sum.inl i))))
    {F : HsConfiguration M → ℝ} {G : HsConfiguration M → HsEuclidean M}
    (hFG : WeightedSobolev.IsGraphH1
      (blockQuotientMarginal χ hc e hmono he0 : Measure _)
      (fun _ : hsSmoothCore M => True) (fun f => hsSmoothValue f.val) hsSmoothGradient F G)
    (hzero : ∀ᵐ x ∂(blockQuotientMarginal χ hc e hmono he0 : Measure _),
      inner ℝ (G x) (hsUnitVector M) = 0)
    {L : ℝ} (hL : ∀ᵐ x ∂(blockQuotientMarginal χ hc e hmono he0 : Measure _), ‖G x‖ ≤ L)
    (t : ℝ) :
    let μI : Measure (HsConfiguration M) := blockQuotientMarginal χ hc e hmono he0
    Integrable F μI ∧ Integrable (fun x => Real.exp (t * F x)) μI ∧
      Real.log (∫ x, Real.exp (t * F x) ∂μI) ≤
        t * (∫ x, F x ∂μI) + t ^ 2 * L ^ 2 / (2 * c₁ * M) := by
  let basis := stdOrthonormalBasis ℝ (hsOrthSubspace M)
  clear_value basis
  let ν := (volume.restrict (scalarPoincareRadialDomain basis)).tilted
    (fun q => -blockRadialPotential χ e basis q)
  let μI : Measure (HsConfiguration M) := blockQuotientMarginal χ hc e hmono he0
  let C := blockQuotientProductCoord basis
  have hmap : μI.map C = ν.prod AddCircle.haarAddCircle :=
    blockQuotientProjection_map_product hPL χ hc e hmono he0 basis
  have hC : MeasurableEmbedding C := measurableEmbedding_blockQuotientProductCoord basis
  have hCP : MeasurePreserving C μI (ν.prod AddCircle.haarAddCircle) := ⟨hC.measurable, hmap⟩
  obtain ⟨F', G', hprod, heF, heG⟩ := block_quotient_graph_transport basis hFG
  change ∀ x, F' (C x) = F x at heF
  change ∀ x, G' (C x) = G x at heG
  change WeightedSobolev.IsGraphH1 (μI.map C) _ _ _ F' G' at hprod
  change ∀ᵐ x ∂μI, inner ℝ (G x) (hsUnitVector M) = 0 at hzero
  change ∀ᵐ x ∂μI, ‖G x‖ ≤ L at hL
  rw [hmap] at hprod
  have hzero' : ∀ᵐ p ∂ν.prod AddCircle.haarAddCircle,
      inner ℝ (G' p) (hsUnitVector M) = 0 := by
    rw [← hmap]
    apply hC.ae_map_iff.mpr
    simpa only [heG] using hzero
  have hL' : ∀ᵐ p ∂ν.prod AddCircle.haarAddCircle, ‖G' p‖ ≤ L := by
    rw [← hmap]
    apply hC.ae_map_iff.mpr
    simpa only [heG] using hL
  obtain ⟨hFp, hEp, hmgf⟩ :=
    block_product_concentration hBE hPL χ hc hc₁ e hmono he0 basis hcurv hprod hzero' hL' t
  have hFμI : Integrable F μI := by
    have hh := hCP.integrable_comp_of_integrable hFp
    simpa only [Function.comp_def, heF] using hh
  have hEμI : Integrable (fun x => Real.exp (t * F x)) μI := by
    have hh := hCP.integrable_comp_of_integrable hEp
    simpa only [Function.comp_def, heF] using hh
  have hmean := hCP.integral_comp hC F'
  simp only [heF] at hmean
  have hmexp := hCP.integral_comp hC (fun p => Real.exp (t * F' p))
  simp only [heF] at hmexp
  refine ⟨hFμI, hEμI, ?_⟩
  rw [hmexp, hmean]
  exact hmgf

/-- Circular block concentration for any increasing retained set containing the first
label. Sobolev descent, exponential integrability and normalization are proved internally.
No admissibility or lower bound on the block size beyond nonemptiness is needed. -/
theorem block_concentration_retained (hBE : External.BakryEmery)
    (hPL : External.PrekopaLeindler) (χ : HsPairPotentials N c) (hc : 0 < c) (hc₁ : 0 < c₁)
    (e : Fin (M : ℕ) ⊕ Fin n ≃ Fin (N : ℕ))
    (hmono : StrictMono fun a => e (Sum.inl a))
    (he0 : e (Sum.inl ⟨0, M.pos⟩) = ⟨0, N.pos⟩)
    (hcurv : ∀ x ∈ hsChamber N, ∀ i j : Fin (M : ℕ), i < j → c₁ / 2 ≤
      deriv (deriv (χ.potential (e (Sum.inl i)) (e (Sum.inl j))))
        (x (e (Sum.inl j)) - x (e (Sum.inl i))))
    {F : HsConfiguration M → ℝ} {G : HsConfiguration M → HsEuclidean M}
    (hFG : WeightedSobolev.IsGraphH1
      (blockQuotientMarginal χ hc e hmono he0 : Measure _)
      (fun _ : hsSmoothCore M => True) (fun f => hsSmoothValue f.val) hsSmoothGradient F G)
    (hzero : ∀ᵐ x ∂(blockQuotientMarginal χ hc e hmono he0 : Measure _),
      inner ℝ (G x) (hsUnitVector M) = 0)
    {L : ℝ} (hL : ∀ᵐ x ∂(blockQuotientMarginal χ hc e hmono he0 : Measure _), ‖G x‖ ≤ L)
    (t : ℝ) :
    Integrable (fun X => F (blockQuotientProjection e hmono he0 X))
      (hsGibbsProbability χ hc : Measure _) ∧
    Integrable (fun X => Real.exp (t * F (blockQuotientProjection e hmono he0 X)))
      (hsGibbsProbability χ hc : Measure _) ∧
    Real.log (∫ X, Real.exp (t * F (blockQuotientProjection e hmono he0 X))
      ∂(hsGibbsProbability χ hc : Measure _)) ≤
      t * (∫ X, F (blockQuotientProjection e hmono he0 X)
        ∂(hsGibbsProbability χ hc : Measure _)) + t ^ 2 * L ^ 2 / (2 * c₁ * M) := by
  obtain ⟨hFi, hEi, hmgf⟩ := block_marginal_concentration
    hBE hPL χ hc hc₁ e hmono he0 hcurv hFG hzero hL t
  let μI : Measure (HsConfiguration M) := blockQuotientMarginal χ hc e hmono he0
  have hπ : MeasurePreserving (blockQuotientProjection e hmono he0)
      (hsGibbsProbability χ hc : Measure _) μI :=
    ⟨measurable_blockQuotientProjection e hmono he0, rfl⟩
  obtain ⟨hF, hv⟩ := integrable_integral_comp_measurePreserving hπ hFi
  obtain ⟨hE, he⟩ := integrable_integral_comp_measurePreserving hπ hEi
  refine ⟨hF, hE, ?_⟩
  rw [he, hv]
  exact hmgf

/-- The retained-block estimate on the Hilbert completion, with the
zero-sum weak derivative condition of the paper. The conclusion is under the original Gibbs law. -/
theorem block_concentration_retained_H1 (hBE : External.BakryEmery)
    (hPL : External.PrekopaLeindler) (χ : HsPairPotentials N c) (hc : 0 < c) (hc₁ : 0 < c₁)
    (e : Fin (M : ℕ) ⊕ Fin n ≃ Fin (N : ℕ))
    (hmono : StrictMono fun a => e (Sum.inl a))
    (he0 : e (Sum.inl ⟨0, M.pos⟩) = ⟨0, N.pos⟩)
    (hcurv : ∀ x ∈ hsChamber N, ∀ i j : Fin (M : ℕ), i < j → c₁ / 2 ≤
      deriv (deriv (χ.potential (e (Sum.inl i)) (e (Sum.inl j))))
        (x (e (Sum.inl j)) - x (e (Sum.inl i))))
    (f : HsSobolev (blockQuotientMarginal χ hc e hmono he0 : Measure _))
    (hzero : ∀ᵐ x ∂(blockQuotientMarginal χ hc e hmono he0 : Measure _),
      ∑ i, hsSobolevGradient _ f x i = 0)
    {L : ℝ} (hL : ∀ᵐ x ∂(blockQuotientMarginal χ hc e hmono he0 : Measure _),
      ‖hsSobolevGradient _ f x‖ ≤ L) (t : ℝ) :
    let F := fun X => hsSobolevValue _ f (blockQuotientProjection e hmono he0 X)
    Integrable F (hsGibbsProbability χ hc : Measure _) ∧
      Integrable (fun X => Real.exp (t * F X)) (hsGibbsProbability χ hc : Measure _) ∧
      Real.log (∫ X, Real.exp (t * F X) ∂(hsGibbsProbability χ hc : Measure _)) ≤
        t * (∫ X, F X ∂(hsGibbsProbability χ hc : Measure _)) + t ^ 2 * L ^ 2 / (2 * c₁ * M) := by
  let μI : Measure (HsConfiguration M) := blockQuotientMarginal χ hc e hmono he0
  have hgraph := (hsSobolev_iff_graph μI (hsSobolevValue μI f) (hsSobolevGradient μI f)
    (Lp.memLp _) (Lp.memLp _)).mp (by
      simp only [Lp.toLp_coeFn]
      change WithLp.toLp 2 ((WithLp.ofLp f.val).1, (WithLp.ofLp f.val).2) ∈ hsSobolevSubmodule μI
      simpa only [Prod.mk.eta, WithLp.toLp_ofLp] using f.property)
  apply block_concentration_retained hBE hPL χ hc hc₁ e hmono he0 hcurv hgraph
    (hL := hL)
  filter_upwards [hzero] with x hx
  have he : inner ℝ (hsSobolevGradient μI f x) (hsUnitVector M) =
      (Real.sqrt (M : ℕ))⁻¹ * ∑ i, hsSobolevGradient μI f x i := by
    simp [hsUnitVector, hsRotationVector, PiLp.inner_apply, inner_smul_right, Finset.mul_sum]
  rw [he, hx, mul_zero]

end Internal

end Riesz1

end
