/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.IntegrationByPartsLocal
public import Riesz1.HelfferSjostrand.IntegrationByPartsPairing
public import Riesz1.HelfferSjostrand.SobolevDensity

/-!
# Local weak identities for the periodic Sobolev completion

The weighted distributional identity extends to the completed jets by
continuity. Compact interior tests then detect a zero limiting gradient.
This supplies the closability assertion for the completion.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter Topology
open scoped ContDiff

namespace Riesz1

theorem continuous_hsLocalCoefficient {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c)
    {ψ : HsEuclidean N → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψU : tsupport ψ ⊆ hsChamber N) (v : HsEuclidean N) :
    Continuous (fun x => ψ x * fderiv ℝ (hsPairExpression χ) x v - fderiv ℝ ψ x v) := by
  have hH := (hsPairExpression_contDiffOn χ).continuousOn_fderiv_of_isOpen
    (isOpen_hsChamber N) (by norm_num)
  exact (WeightedSobolev.continuous_cutoff_mul (isOpen_hsChamber N) hψ.continuous hψU
    (hH.clm_apply continuousOn_const)).sub
      ((hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const)

/-- The completed gradient satisfies the local weighted weak-derivative identity. -/
theorem hsSobolev_local_integrationByParts {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c)
    (hc : 0 < c)
    (f : HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)))
    {ψ : HsEuclidean N → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ hsChamber N)
    (hψS : tsupport ψ ⊆ {x | x ⟨0, N.pos⟩ ∈ Ioo (0 : ℝ) 1}) (v : HsEuclidean N) :
    ∫ x, hsSmoothValue ψ x * inner ℝ (hsSobolevGradient
        (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) f x) v
        ∂(hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) =
      ∫ x, hsSobolevValue
          (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) f x *
        hsSmoothValue (fun y => ψ y * fderiv ℝ (hsPairExpression χ) y v - fderiv ℝ ψ y v) x
          ∂(hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) := by
  let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
  let b := fun y => ψ y * fderiv ℝ (hsPairExpression χ) y v - fderiv ℝ ψ y v
  change (∫ x, hsSmoothValue ψ x * inner ℝ (hsSobolevGradient μ f x) v ∂μ) =
    ∫ x, hsSobolevValue μ f x * hsSmoothValue b x ∂μ
  have hbLp : MemLp (hsSmoothValue b) 2 μ := memLp_hsLiftPoint (f := b) μ 2
    (continuous_hsLocalCoefficient χ hψ hψU v).continuousOn
  have htLp : MemLp (fun x => hsSmoothValue ψ x • v) 2 μ :=
    memLp_hsLiftPoint (f := fun y => ψ y • v) μ 2
      (hψ.continuous.smul continuous_const).continuousOn
  have hcore (φ : hsSmoothCore N) :
      (∫ x, inner ℝ (hsSmoothGradient φ x) (hsSmoothValue ψ x • v) ∂μ) =
        ∫ x, hsSmoothValue φ.val x * hsSmoothValue b x ∂μ := by
    simp only [inner_smul_right]
    exact hsGibbsLocalIntegrationByParts χ hc φ hψ hψc hψU hψS v
  simpa only [inner_smul_right] using
    Internal.hsSobolev_pairing_of_smooth μ _ htLp _ hbLp hcore f

namespace Internal

theorem hsSobolevGradient_eq_zero_of_value_eq_zero {N : ℕ+} {c : ℝ}
    (χ : HsPairPotentials N c) (hc : 0 < c)
    (f : HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)))
    (hf : hsSobolevValue _ f = 0) : hsSobolevGradient _ f = 0 := by
  let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
  let G := hsSobolevGradient μ f
  let U := hsChamber N ∩ {x : HsEuclidean N | x ⟨0, N.pos⟩ ∈ Ioo (0 : ℝ) 1}
  have hU : IsOpen U := (isOpen_hsChamber N).inter
    (isOpen_Ioo.preimage (EuclideanSpace.proj (𝕜 := ℝ) (⟨0, N.pos⟩ : Fin (N : ℕ))).continuous)
  have hμ : ∀ᵐ x ∂μ, hsLiftPoint N x ∈ U := by
    filter_upwards [hsQuotientGibbsProbability_ae_open_strip χ hc] with x hx
    exact ⟨hsLiftPoint_mem_chamber N x, hx⟩
  have hi (i : Fin (N : ℕ)) : (EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 μ G = 0 := by
    apply eq_zero_of_chart_tests μ (hsLiftPoint N) (measurableEmbedding_hsLiftPoint N) U hU hμ
    intro ψ hψ hψc hψU
    have hloc := hsSobolev_local_integrationByParts χ hc f hψ hψc
      (fun x hx => (hψU hx).1) (fun x hx => (hψU hx).2) (EuclideanSpace.single i 1)
    have hright : (∫ x, hsSobolevValue μ f x * hsSmoothValue
        (fun y => ψ y * fderiv ℝ (hsPairExpression χ) y (EuclideanSpace.single i 1) -
          fderiv ℝ ψ y (EuclideanSpace.single i 1)) x ∂μ) = 0 := by
      rw [hf]
      apply integral_eq_zero_of_ae
      filter_upwards [Lp.coeFn_zero ℝ 2 μ] with x hx
      simp only [hx, Pi.zero_apply, zero_mul]
    calc
      _ = ∫ x, hsSmoothValue ψ x * inner ℝ (G x) (EuclideanSpace.single i 1) ∂μ := by
        apply integral_congr_ae
        filter_upwards [(EuclideanSpace.proj (𝕜 := ℝ) i).coeFn_compLpL G] with x hx
        rw [hx, EuclideanSpace.inner_single_right]
        simp only [RCLike.conj_to_real, one_mul, hsSmoothValue]
        rfl
      _ = _ := hloc
      _ = 0 := hright
  have hcoord (i : Fin (N : ℕ)) : ∀ᵐ x ∂μ, G x i = 0 := by
    have heq := (EuclideanSpace.proj (𝕜 := ℝ) i).coeFn_compLpL (p := 2) (μ := μ) G
    rw [hi i] at heq
    filter_upwards [heq, Lp.coeFn_zero ℝ 2 μ] with x hx h0
    change (EuclideanSpace.proj i) (G x) = 0
    simpa only [h0, Pi.zero_apply] using hx.symm
  apply Lp.ext
  filter_upwards [ae_all_iff.mpr hcoord, Lp.coeFn_zero (HsEuclidean N) 2 μ] with x hx h0
  rw [h0]
  ext i
  exact hx i

end Internal

/-- The Gibbs Sobolev completion injects into scalar `L²`.
Pair curvature and boundary growth are unnecessary for this local argument. -/
theorem hsSobolevValue_injective {N : ℕ+} {c : ℝ}
    (χ : HsPairPotentials N c) (hc : 0 < c) :
    Function.Injective (hsSobolevValue
      (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))) := by
  intro f g hfg
  let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
  have hv : hsSobolevValue μ (f - g) = 0 := by rw [map_sub, hfg, sub_self]
  have hg := Internal.hsSobolevGradient_eq_zero_of_value_eq_zero χ hc (f - g) hv
  have hz : f - g = 0 := by
    apply Subtype.ext
    apply (WithLp.equiv 2 _).injective
    apply Prod.ext
    · exact hv
    · exact hg
  exact sub_eq_zero.mp hz

end Riesz1

end
