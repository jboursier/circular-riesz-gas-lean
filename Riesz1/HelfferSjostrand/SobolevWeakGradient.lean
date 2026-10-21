/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.SobolevSeam

/-!
# Inverse-density distributional tests across the seam

The ordinary weak-gradient identity can be expressed on the quotient by
periodizing each compact cover test after multiplying it by `exp H`.
This cancels the Gibbs density. The Hamiltonian derivative cancels from
the weak identity. There is no restriction on the rotation coordinate
of the compact test, so seam-crossing charts are included.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter Topology
open scoped ContDiff

namespace Riesz1

/-- The ordinary distributional-gradient identity in inverse-density
periodized tests. Every compact interior cover test is allowed. -/
theorem hsSobolev_weakGradient {N : ℕ+} {c : ℝ}
    (hN : 2 ≤ (N : ℕ)) (χ : HsPairPotentials N c) (hc : 0 < c)
    (f : HsSobolev (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)))
    {ψ : HsEuclidean N → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ hsChamber N) (v : HsEuclidean N) :
    let A := vectorPeriodize (hsRotationVector N) (hsRotationVector_ne_zero N)
      (fun y => ψ y * Real.exp (hsPairExpression χ y)) hψc.mul_right
    let B := vectorPeriodize (hsRotationVector N) (hsRotationVector_ne_zero N)
      (fun y => fderiv ℝ ψ y v * Real.exp (hsPairExpression χ y))
      (hψc.fderiv_apply ℝ v).mul_right
    ∫ x, hsSmoothValue A x * inner ℝ (hsSobolevGradient
        (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) f x) v
        ∂(hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) =
      -(∫ x, hsSobolevValue
          (hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) f x *
        hsSmoothValue B x
          ∂(hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))) := by
  let η := fun y => ψ y * Real.exp (hsPairExpression χ y)
  let ρ := fun y => fderiv ℝ ψ y v * Real.exp (hsPairExpression χ y)
  have hη : ContDiff ℝ ∞ η := WeightedSobolev.contDiff_cutoff_mul
    (isOpen_hsChamber N) hψ hψU (hsPairExpression_contDiffOn χ).exp
  have hηc : HasCompactSupport η := hψc.mul_right
  have hηU : tsupport η ⊆ hsChamber N := tsupport_mul_subset_left.trans hψU
  have hρc : HasCompactSupport ρ := (hψc.fderiv_apply ℝ v).mul_right
  have hd (y : HsEuclidean N) :
      η y * fderiv ℝ (hsPairExpression χ) y v - fderiv ℝ η y v = -ρ y := by
    by_cases hy : y ∈ hsChamber N
    · have hH := ((hsPairExpression_contDiffOn χ).contDiffAt
        ((isOpen_hsChamber N).mem_nhds hy)).differentiableAt (by norm_num)
      have he := ((hψ.differentiable (by norm_num) y).hasFDerivAt.mul hH.hasFDerivAt.exp).fderiv
      change fderiv ℝ η y = _ at he
      rw [he]
      simp only [η, ρ, add_apply, smul_apply, smul_eq_mul]
      ring
    · have hys : y ∉ tsupport ψ := fun hh => hy (hψU hh)
      have hyη : y ∉ tsupport η := fun hh => hys (tsupport_mul_subset_left hh)
      simp only [fderiv_of_notMem_tsupport ℝ hyη, zero_apply, η,
        image_eq_zero_of_notMem_tsupport hys, zero_mul, sub_zero, ρ,
        fderiv_of_notMem_tsupport ℝ hys, neg_zero]
  let A := vectorPeriodize (hsRotationVector N) (hsRotationVector_ne_zero N) η hηc
  let B := vectorPeriodize (hsRotationVector N) (hsRotationVector_ne_zero N) ρ hρc
  have hHp (k : ℤ) (y : HsEuclidean N) :
      fderiv ℝ (hsPairExpression χ) (y + (k : ℝ) • hsRotationVector N) =
        fderiv ℝ (hsPairExpression χ) y :=
    fderiv_periodic_vector (fun k y => by
      rw [← hsTranslate_eq_add_rotation]; exact hsPairExpression_translate χ _ _) k y
  have hq (y : HsEuclidean N) :
      A y * fderiv ℝ (hsPairExpression χ) y v - fderiv ℝ A y v = -B y := by
    rw [fderiv_vectorPeriodize_apply (hsRotationVector_ne_zero N)
      (hη.differentiable (by norm_num)) hηc]
    change (∑ᶠ k : ℤ, η (y + (k : ℝ) • hsRotationVector N)) *
      fderiv ℝ (hsPairExpression χ) y v -
      (∑ᶠ k : ℤ, fderiv ℝ η (y + (k : ℝ) • hsRotationVector N) v) = -B y
    rw [finsum_mul]
    have hfin : HasFiniteSupport (fun k : ℤ => η (y + (k : ℝ) • hsRotationVector N) *
        fderiv ℝ (hsPairExpression χ) y v) := by
      have hh : HasCompactSupport (fun z => η z * fderiv ℝ (hsPairExpression χ) z v) :=
        hηc.mul_right
      simpa only [hHp] using (vectorPeriodize_finite_support (hsRotationVector_ne_zero N) hh y)
    rw [← finsum_sub_distrib hfin
      (vectorPeriodize_finite_support (hsRotationVector_ne_zero N) (hηc.fderiv_apply ℝ v) y)]
    have he : (fun k : ℤ => η (y + (k : ℝ) • hsRotationVector N) *
        fderiv ℝ (hsPairExpression χ) y v -
        fderiv ℝ η (y + (k : ℝ) • hsRotationVector N) v) =
        (fun k : ℤ => -ρ (y + (k : ℝ) • hsRotationVector N)) := by
      funext k
      rw [← hHp k y]
      exact hd _
    rw [he]
    rw [finsum_neg_distrib]
    rfl
  have hi := hsSobolev_periodized_integrationByParts hN χ hc f hη hηc hηU v
  dsimp only at hi ⊢
  change (∫ x, hsSmoothValue A x * inner ℝ (hsSobolevGradient _ f x) v ∂_) = _
  rw [hi, ← integral_neg]
  apply integral_congr_ae
  filter_upwards with x
  change hsSobolevValue _ f x * (A (hsLiftPoint N x) *
      fderiv ℝ (hsPairExpression χ) (hsLiftPoint N x) v -
      fderiv ℝ A (hsLiftPoint N x) v) =
    -(hsSobolevValue _ f x * B (hsLiftPoint N x))
  rw [hq, mul_neg]

end Riesz1

end
