/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.SobolevPeriodization
public import Riesz1.ToMathlib.WeightedSobolev.TestDensity

/-!
# Density of the periodic Sobolev space in scalar L²

Compact smooth tests in
the open fundamental strip are periodized into the smooth core.
The Gibbs law gives zero mass to the omitted seam.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Topology
open scoped ContDiff ENNReal

namespace Riesz1

theorem hsLiftPoint_injective (N : ℕ+) : Function.Injective (hsLiftPoint N) := by
  intro x y h
  apply (hsConfigurationEquiv N).symm.injective
  apply Subtype.ext
  exact congrArg WithLp.ofLp h

theorem measurableEmbedding_hsLiftPoint (N : ℕ+) : MeasurableEmbedding (hsLiftPoint N) := by
  exact (PiLp.homeomorph 2 (fun _ : Fin (N : ℕ) => ℝ)).symm.measurableEmbedding.comp
    ((MeasurableEmbedding.subtype_coe (measurableSet_orderedDomain N)).comp
      (hsConfigurationMeasurableEquiv N).symm.measurableEmbedding)

theorem hsGibbsProbability_absolutelyContinuous {N : ℕ+} {c : ℝ}
    (χ : HsPairPotentials N c) (hc : 0 < c) :
    (hsGibbsProbability χ hc : Measure (Configuration N)) ≪ configurationVolume N :=
  (withDensity_absolutelyContinuous _ _).smul_left _

theorem hsQuotientGibbsProbability_ae_open_strip {N : ℕ+} {c : ℝ}
    (χ : HsPairPotentials N c) (hc : 0 < c) :
    ∀ᵐ x ∂(hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)),
      hsLiftPoint N x ⟨0, N.pos⟩ ∈ Ioo (0 : ℝ) 1 := by
  have hz : ∀ᵐ X ∂configurationVolume N, X.val ⟨0, N.pos⟩ ≠ 0 := by
    have hv : ∀ᵐ x ∂(volume : Measure (Fin (N : ℕ) → ℝ)), x ⟨0, N.pos⟩ ≠ 0 := by
      rw [ae_iff]
      rw [volume_pi]
      convert (Measure.pi_eval_preimage_null (fun _ : Fin (N : ℕ) => (volume : Measure ℝ))
        (i := ⟨0, N.pos⟩) (measure_singleton (0 : ℝ))) using 2
      ext x
      simp
    exact (ae_restrict_iff_subtype (measurableSet_orderedDomain N)).mp
      (ae_restrict_of_ae hv)
  rw [hsQuotientGibbsProbability_eq_map]
  apply (measurableEmbedding_hsConfigurationMap N).ae_map_iff.mpr
  filter_upwards [(hsGibbsProbability_absolutelyContinuous χ hc).ae_le hz] with X hX
  change (WithLp.toLp 2 ((hsConfigurationEquiv N).symm
    ((hsConfigurationEquiv N) X)).val) ⟨0, N.pos⟩ ∈ Ioo (0 : ℝ) 1
  rw [Equiv.symm_apply_apply]
  exact ⟨lt_of_le_of_ne X.property.2.1 (Ne.symm hX), X.property.2.2.1⟩

namespace Internal

/-- This helper isolates the seam-null condition. The Gibbs theorem below
derives it from absolute continuity rather than assuming density. -/
theorem denseRange_hsSobolevValue_of_open_strip {N : ℕ+}
    (μ : Measure (HsConfiguration N)) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ x ∂μ, hsLiftPoint N x ⟨0, N.pos⟩ ∈ Ioo (0 : ℝ) 1) :
    DenseRange (hsSobolevValue μ) := by
  apply denseRange_of_chart_tests μ (hsSobolevValue μ).toLinearMap
    (hsLiftPoint N) (measurableEmbedding_hsLiftPoint N)
    {x | x ⟨0, N.pos⟩ ∈ Ioo (0 : ℝ) 1}
    (isOpen_Ioo.preimage (EuclideanSpace.proj (𝕜 := ℝ) (⟨0, N.pos⟩ : Fin (N : ℕ))).continuous) hμ
  intro g hg hgc hgU
  let φ : hsSmoothCore N := ⟨_, hsSmoothOnClosure_vectorPeriodize hg hgc⟩
  refine ⟨hsSobolevOfSmooth μ φ, ?_⟩
  have hval : hsSobolevValue μ (hsSobolevOfSmooth μ φ) =
      (φ.property.memLp_value μ).toLp (hsSmoothValue φ.val) := rfl
  change (hsSobolevValue μ (hsSobolevOfSmooth μ φ) : HsConfiguration N → ℝ) =ᵐ[μ] _
  rw [hval]
  convert (φ.property.memLp_value μ).coeFn_toLp using 1
  rw [show hsSmoothValue φ.val = hsSmoothValue g from
    hsSmoothValue_vectorPeriodize hgc (subset_trans subset_closure hgU)]
  rfl

end Internal

/-- `H¹(μ)` has dense image in `L²(μ)` for the Gibbs probability.
The boundary-growth condition is unnecessary for this claim. -/
theorem denseRange_hsSobolevValue {N : ℕ+} {c : ℝ}
    (χ : HsPairPotentials N c) (hc : 0 < c) :
    DenseRange (hsSobolevValue
      (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))) :=
  Internal.denseRange_hsSobolevValue_of_open_strip _
    (hsQuotientGibbsProbability_ae_open_strip χ hc)

end Riesz1

end
