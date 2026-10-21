/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.QuotientChartL2
public import Riesz1.HelfferSjostrand.QuotientChartUnfolding

/-!
# Unweighted unfolding for the scalar boundary core

Periodized compact interior tests unfold against arbitrary locally
integrable periodic representatives, including quotient L² classes.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter Topology

namespace Riesz1

/-- Unweighted quotient integration through the unique fundamental lift. -/
theorem hsConfigurationVolume_integral_lift {N : ℕ+} (f : HsEuclidean N → ℝ) :
    ∫ x, hsSmoothValue f x ∂hsConfigurationVolume N =
      ∫ y in hsFundamentalRegion N, f y := by
  rw [← (measurePreserving_hsLiftPoint_volume N).map_eq,
    (measurableEmbedding_hsLiftPoint N).integral_map]
  rfl

/-- Unfolding against a locally integrable periodic coefficient. The compact
interior test may cross any integer rotation seam. -/
theorem hsVolumeIntegral_periodized_test_locallyIntegrable {N : ℕ+}
    {ψ b : HsEuclidean N → ℝ}
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ hsChamber N)
    (hb : LocallyIntegrableOn b (hsChamber N))
    (hbp : ∀ (k : ℤ) x, b (hsTranslate (k : ℝ) x) = b x) :
    ∫ x, hsSmoothValue
        (vectorPeriodize (hsRotationVector N) (hsRotationVector_ne_zero N) ψ hψc) x *
        hsSmoothValue b x ∂hsConfigurationVolume N = ∫ y, ψ y * b y := by
  let v := hsRotationVector N
  let hv := hsRotationVector_ne_zero N
  let P := vectorPeriodize v hv ψ hψc
  let ℓ := EuclideanSpace.proj (𝕜 := ℝ) (⟨0, N.pos⟩ : Fin (N : ℕ))
  let S := ℓ ⁻¹' Ico (0 : ℝ) 1
  have hℓ : ℓ v = 1 := by simp [ℓ, v, hsRotationVector]
  have hi : Integrable (fun y => ψ y * b y) := by
    simpa only [smul_eq_mul] using integrable_smul_of_compact_interior hb hψ hψc hψU
  have hPzero (x : HsEuclidean N) (hx : x ∉ hsChamber N) : P x = 0 :=
    vectorPeriodize_eq_zero_of_not_mem hv hψc
      (fun k y => by rw [← hsTranslate_eq_add_rotation]; exact hsTranslate_mem_chamber_iff _ _)
      ((subset_closure : support ψ ⊆ tsupport ψ).trans hψU) hx
  change (∫ x, hsSmoothValue (fun y => P y * b y) x ∂hsConfigurationVolume N) = _
  rw [hsConfigurationVolume_integral_lift]
  have hF : hsFundamentalRegion N = hsChamber N ∩ S := rfl
  rw [hF, ← Measure.restrict_restrict (isOpen_hsChamber N).measurableSet]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
    simp only [hPzero y hy, zero_mul])]
  exact integral_vectorPeriodize_mul_periodic hv ℓ hℓ hψc
    (fun k y => by rw [← hsTranslate_eq_add_rotation]; exact hbp k y) hi

end Riesz1
