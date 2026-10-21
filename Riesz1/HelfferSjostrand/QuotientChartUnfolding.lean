/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.SobolevGibbsIntegrals
public import Riesz1.ToMathlib.EllipticRegularity.WeakOperations
public import Riesz1.HelfferSjostrand.SobolevPeriodization
public import Riesz1.ToMathlib.Chamber.PeriodizationIntegral
public import Riesz1.ToMathlib.Chamber.PeriodizationDerivative
public import Riesz1.ToMathlib.WeightedSobolev.LocalIntegrationByParts

/-!
# Gibbs unfolding with locally integrable periodic coefficients

Integration of a periodized interior test against a periodic coefficient
unfolds to integration on the entire Euclidean cover. No open-strip
support condition is imposed on the original compact test.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter Topology
open scoped ContDiff

namespace Riesz1

/-- Exact weighted unfolding for arbitrary locally integrable periodic
coefficients, including completed L² representatives. -/
theorem hsGibbsIntegral_periodized_test_locallyIntegrable {N : ℕ+} {c : ℝ}
    (χ : HsPairPotentials N c) (hc : 0 < c) {ψ b : HsEuclidean N → ℝ}
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ hsChamber N)
    (hb : LocallyIntegrableOn b (hsChamber N))
    (hbp : ∀ (k : ℤ) x, b (hsTranslate (k : ℝ) x) = b x) :
    ∫ x, hsSmoothValue
        (vectorPeriodize (hsRotationVector N) (hsRotationVector_ne_zero N) ψ hψc) x *
        hsSmoothValue b x
        ∂(hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) =
      ((hsPartitionFunction χ)⁻¹).toReal *
        ∫ y, ψ y * (Real.exp (-hsPairExpression χ y) * b y) := by
  let v := hsRotationVector N
  let hv := hsRotationVector_ne_zero N
  let P := vectorPeriodize v hv ψ hψc
  let ℓ := EuclideanSpace.proj (𝕜 := ℝ) (⟨0, N.pos⟩ : Fin (N : ℕ))
  let S := ℓ ⁻¹' Ico (0 : ℝ) 1
  let w := fun y => Real.exp (-hsPairExpression χ y) * b y
  have hℓ : ℓ v = 1 := by simp [ℓ, v, hsRotationVector]
  have hη : Continuous (fun y => ψ y * Real.exp (-hsPairExpression χ y)) :=
    WeightedSobolev.continuous_cutoff_mul (isOpen_hsChamber N) hψ hψU
      (Real.continuous_exp.comp_continuousOn (hsPairExpression_contDiffOn χ).continuousOn.neg)
  have hi : Integrable (fun y => ψ y * w y) := by
    have hh := integrable_smul_of_compact_interior hb hη hψc.mul_right
      (tsupport_mul_subset_left.trans hψU)
    simpa only [w, smul_eq_mul, mul_assoc] using hh
  have hwp (k : ℤ) (x : HsEuclidean N) : w (x + (k : ℝ) • v) = w x := by
    rw [← hsTranslate_eq_add_rotation]
    simp only [w, hsPairExpression_translate, hbp]
  have hPzero (x : HsEuclidean N) (hx : x ∉ hsChamber N) : P x = 0 :=
    vectorPeriodize_eq_zero_of_not_mem hv hψc
      (fun k y => by rw [← hsTranslate_eq_add_rotation]; exact hsTranslate_mem_chamber_iff _ _)
      ((subset_closure : support ψ ⊆ tsupport ψ).trans hψU) hx
  change (∫ x, hsSmoothValue (fun y => P y * b y) x
    ∂(hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))) = _
  rw [hsQuotientGibbsProbability_integral]
  congr 1
  have hF : hsFundamentalRegion N = hsChamber N ∩ S := by
    ext y
    rfl
  rw [hF, ← Measure.restrict_restrict (isOpen_hsChamber N).measurableSet]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
    simp only [hPzero y hy, zero_mul, mul_zero])]
  calc
    _ = ∫ y in S, P y * w y := by
      apply integral_congr_ae
      filter_upwards with y
      dsimp [w]
      ring
    _ = _ := integral_vectorPeriodize_mul_periodic hv ℓ hℓ hψc hwp hi

end Riesz1

end
