/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.SobolevSeamIntegrals
public import Riesz1.HelfferSjostrand.SobolevClosability
public import Riesz1.HelfferSjostrand.IntegrationByPartsBounds

/-!
# Weighted weak identities across the periodic seam

Compact interior tests on the Euclidean cover can cross any integer
seam. Periodization unfolds their weighted weak identities exactly.
The identity extends continuously to the entire Sobolev completion.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter Topology
open scoped ContDiff

namespace Riesz1

/-- Smooth weighted integration by parts for arbitrary periodized interior tests. -/
theorem hsGibbsPeriodizedIntegrationByParts {N : ℕ+} {c : ℝ}
    (χ : HsPairPotentials N c) (hc : 0 < c) (φ : hsSmoothCore N)
    {ψ : HsEuclidean N → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ hsChamber N) (v : HsEuclidean N) :
    let P := vectorPeriodize (hsRotationVector N) (hsRotationVector_ne_zero N) ψ hψc
    ∫ x, hsSmoothValue P x * inner ℝ (hsSmoothGradient φ x) v
        ∂(hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) =
      ∫ x, hsSmoothValue φ.val x * hsSmoothValue
        (fun y => P y * fderiv ℝ (hsPairExpression χ) y v - fderiv ℝ P y v) x
          ∂(hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) := by
  let hV := hsRotationVector_ne_zero N
  let P := vectorPeriodize (hsRotationVector N) hV ψ hψc
  let q := fun y => ψ y * fderiv ℝ (hsPairExpression χ) y v - fderiv ℝ ψ y v
  have hqc : HasCompactSupport q := hψc.mul_right.sub (hψc.fderiv_apply ℝ v)
  have hqcont : Continuous q := continuous_hsLocalCoefficient χ hψ hψU v
  have hqU : tsupport q ⊆ hsChamber N := by
    refine (show tsupport q ⊆ tsupport ψ from ?_).trans hψU
    apply closure_minimal _ (isClosed_tsupport ψ)
    intro y hy
    by_contra hyψ
    exact hy (by simp [q, image_eq_zero_of_notMem_tsupport hyψ,
      fderiv_of_notMem_tsupport ℝ hyψ])
  have hHp (k : ℤ) (y : HsEuclidean N) :
      fderiv ℝ (hsPairExpression χ) (y + (k : ℝ) • hsRotationVector N) = fderiv ℝ (hsPairExpression χ) y :=
    fderiv_periodic_vector (fun k y => by
      rw [← hsTranslate_eq_add_rotation]; exact hsPairExpression_translate χ _ _) k y
  have hqP (y : HsEuclidean N) : vectorPeriodize (hsRotationVector N) hV q hqc y =
      P y * fderiv ℝ (hsPairExpression χ) y v - fderiv ℝ P y v := by
    rw [fderiv_vectorPeriodize_apply hV (hψ.differentiable (by norm_num)) hψc]
    change (∑ᶠ k : ℤ, q (y + (k : ℝ) • hsRotationVector N)) = _
    simp only [q, hHp]
    have hfin : HasFiniteSupport
        (fun k : ℤ => ψ (y + (k : ℝ) • hsRotationVector N) * fderiv ℝ (hsPairExpression χ) y v) := by
      have hh : HasCompactSupport (fun z => ψ z * fderiv ℝ (hsPairExpression χ) z v) :=
        hψc.mul_right
      simpa only [hHp] using (vectorPeriodize_finite_support hV hh y)
    rw [finsum_sub_distrib hfin
      (vectorPeriodize_finite_support hV (hψc.fderiv_apply ℝ v) y)]
    rw [← finsum_mul]
    rfl
  have hφ : ContDiffOn ℝ ∞ φ.val (hsChamber N) := by
    obtain ⟨_, U, _, hU, hφ⟩ := φ.property
    exact hφ.mono (fun _ hx => hU (subset_closure hx))
  have hφp (k : ℤ) (y : HsEuclidean N) :
      fderiv ℝ φ.val (hsTranslate (k : ℝ) y) v = fderiv ℝ φ.val y v := by
    rw [hsTranslate_eq_add_rotation]
    exact congrArg (fun A : HsEuclidean N →L[ℝ] ℝ => A v)
      (fderiv_periodic_vector (fun k y => by
        rw [← hsTranslate_eq_add_rotation]; exact φ.property.1 k y) k y)
  simp only [hsSmoothGradient, inner_gradient_left]
  change (∫ x, hsSmoothValue P x * hsSmoothValue (fun y => fderiv ℝ φ.val y v) x
      ∂(hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))) = _
  rw [hsGibbsIntegral_periodized_test χ hc hψ.continuous hψc hψU
    ((hφ.continuousOn_fderiv_of_isOpen (isOpen_hsChamber N) (by norm_num)).clm_apply
      continuousOn_const) hφp]
  have hr := hsGibbsIntegral_periodized_test χ hc hqcont hqc hqU hφ.continuousOn φ.property.1
  have hr' : (∫ x, hsSmoothValue φ.val x * hsSmoothValue
      (fun y => P y * fderiv ℝ (hsPairExpression χ) y v - fderiv ℝ P y v) x
      ∂(hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))) =
      ((hsPartitionFunction χ)⁻¹).toReal *
        ∫ y, q y * (Real.exp (-hsPairExpression χ y) * φ.val y) := by
    rw [← hr]
    apply integral_congr_ae
    filter_upwards with x
    simp only [hsSmoothValue, hqP, mul_comm]
  rw [hr']
  congr 1
  calc
    _ = ∫ y, (ψ y * Real.exp (-hsPairExpression χ y)) * fderiv ℝ φ.val y v := by
      apply integral_congr_ae
      filter_upwards with y
      ring
    _ = _ := hsLocalIntegrationByParts χ φ hψ hψc hψU v
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with y
      dsimp [q]
      ring

/-- The completion satisfies weighted weak identities for all compact interior
cover tests, without any restriction excluding the seam. -/
theorem hsSobolev_periodized_integrationByParts {N : ℕ+} {c : ℝ}
    (hN : 2 ≤ (N : ℕ)) (χ : HsPairPotentials N c) (hc : 0 < c)
    (f : HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)))
    {ψ : HsEuclidean N → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ hsChamber N) (v : HsEuclidean N) :
    let P := vectorPeriodize (hsRotationVector N) (hsRotationVector_ne_zero N) ψ hψc
    ∫ x, hsSmoothValue P x * inner ℝ (hsSobolevGradient
        (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) f x) v
        ∂(hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) =
      ∫ x, hsSobolevValue
          (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) f x *
        hsSmoothValue (fun y => P y * fderiv ℝ (hsPairExpression χ) y v - fderiv ℝ P y v) x
          ∂(hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) := by
  let μ : Measure (HsConfiguration N) := hsQuotientGibbsProbability χ hc
  let P := vectorPeriodize (hsRotationVector N) (hsRotationVector_ne_zero N) ψ hψc
  let b := fun y => P y * fderiv ℝ (hsPairExpression χ) y v - fderiv ℝ P y v
  have hP := contDiff_vectorPeriodize (hsRotationVector_ne_zero N) hψ hψc
  have hPU : tsupport P ⊆ hsChamber N :=
    (hsTestFunctionOfCompact hN hψ hψc hψU).tsupport_subset_chamber hN
  have hbLp : MemLp (hsSmoothValue b) 2 μ := memLp_hsLiftPoint μ 2
    (continuous_hsLocalCoefficient χ hP hPU v).continuousOn
  have htLp : MemLp (fun x => hsSmoothValue P x • v) 2 μ :=
    memLp_hsLiftPoint (f := fun y => P y • v) μ 2
      (hP.continuous.smul continuous_const).continuousOn
  have hcore (φ : hsSmoothCore N) :
      (∫ x, inner ℝ (hsSmoothGradient φ x) (hsSmoothValue P x • v) ∂μ) =
        ∫ x, hsSmoothValue φ.val x * hsSmoothValue b x ∂μ := by
    simp only [inner_smul_right]
    exact hsGibbsPeriodizedIntegrationByParts χ hc φ hψ hψc hψU v
  simpa only [inner_smul_right] using
    Internal.hsSobolev_pairing_of_smooth μ _ htLp _ hbLp hcore f

end Riesz1

end
