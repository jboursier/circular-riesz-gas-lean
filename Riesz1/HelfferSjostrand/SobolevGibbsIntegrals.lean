/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.Sobolev

/-!
# Scalar integral transport for the periodic Gibbs completion

The real-valued version of the fundamental-region formula, and its
normalized weighted counterpart. These identities use measurable embeddings,
so they apply to every integrand with the usual Bochner integral convention.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped ENNReal

namespace Riesz1

theorem hsFundamentalRegion_integral (N : ℕ+) (f : HsEuclidean N → ℝ) :
    ∫ x in hsFundamentalRegion N, f x =
      ∫ X : Configuration N, f (WithLp.toLp 2 X.val) ∂configurationVolume N := by
  change _ = ∫ X : orderedDomain N, f (WithLp.toLp 2 X.val)
    ∂Measure.comap Subtype.val volume
  rw [integral_subtype_comap (measurableSet_orderedDomain N)
    (fun x => f (WithLp.toLp 2 x))]
  rw [hsFundamentalRegion_eq_preimage]
  have hmap := ((PiLp.volume_preserving_ofLp (Fin (N : ℕ))).restrict_preimage
    (measurableSet_orderedDomain N)).map_eq
  have he : MeasurableEmbedding (WithLp.ofLp : HsEuclidean N → (Fin (N : ℕ) → ℝ)) :=
    (PiLp.homeomorph 2 (fun _ : Fin (N : ℕ) => ℝ)).measurableEmbedding
  rw [← hmap, he.integral_map]

/-- Exact normalized Gibbs integration in the half-open Euclidean fundamental region. -/
theorem hsQuotientGibbsProbability_integral {N : ℕ+} {c : ℝ}
    (χ : HsPairPotentials N c) (hc : 0 < c) (f : HsEuclidean N → ℝ) :
    ∫ x, hsSmoothValue f x
        ∂(hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) =
      ((hsPartitionFunction χ)⁻¹).toReal *
        ∫ x in hsFundamentalRegion N, Real.exp (-hsPairExpression χ x) * f x := by
  rw [hsQuotientGibbsProbability_eq_map,
    (measurableEmbedding_hsConfigurationMap N).integral_map]
  change (∫ X : Configuration N, hsSmoothValue f (hsConfigurationMap N X)
    ∂((hsPartitionFunction χ)⁻¹ • hsFundamentalWeight χ)) = _
  rw [integral_smul_measure]
  have hm : Measurable (fun X : Configuration N =>
      ENNReal.ofReal (Real.exp (-hsFundamentalHamiltonian χ X))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (continuous_hsFundamentalHamiltonian χ).measurable.neg)
  rw [hsFundamentalWeight, integral_withDensity_eq_integral_toReal_smul hm
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  rw [hsFundamentalRegion_integral]
  simp only [smul_eq_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards with X
  change (ENNReal.ofReal (Real.exp (-hsFundamentalHamiltonian χ X))).toReal *
    f (WithLp.toLp 2 ((hsConfigurationEquiv N).symm ((hsConfigurationEquiv N) X)).val) = _
  rw [Equiv.symm_apply_apply, ENNReal.toReal_ofReal (Real.exp_pos _).le]
  rfl

end Riesz1

end
