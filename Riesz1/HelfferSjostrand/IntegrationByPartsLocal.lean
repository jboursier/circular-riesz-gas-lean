/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.SobolevGibbsIntegrals
public import Riesz1.ToMathlib.WeightedSobolev.LocalIntegrationByParts

/-!
# Local Gibbs integration by parts

Compact interior directional tests detect the gradient without a collision
boundary term. The identity here is local on the Euclidean cover, before
periodic-strip endpoint cancellation.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter Topology
open scoped ContDiff

namespace Riesz1

/-- The weighted divergence identity for a compact interior test on the cover. -/
theorem hsLocalIntegrationByParts {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c)
    (φ : hsSmoothCore N) {ψ : HsEuclidean N → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ hsChamber N) (v : HsEuclidean N) :
    ∫ x, (ψ x * Real.exp (-hsPairExpression χ x)) * fderiv ℝ φ.val x v =
      ∫ x, φ.val x * Real.exp (-hsPairExpression χ x) *
        (ψ x * fderiv ℝ (hsPairExpression χ) x v - fderiv ℝ ψ x v) := by
  have hH := hsPairExpression_contDiffOn χ
  have hw : ContDiffOn ℝ ∞ (fun x => Real.exp (-hsPairExpression χ x)) (hsChamber N) :=
    hH.neg.exp
  have hφ : ContDiffOn ℝ ∞ φ.val (hsChamber N) := by
    obtain ⟨_, U, _, hU, hφ⟩ := φ.property
    exact hφ.mono (fun _ hx => hU (subset_closure hx))
  rw [WeightedSobolev.integral_weighted_fderiv_of_compact_test
    (isOpen_hsChamber N) hψ hψc hψU hφ hw v, ← integral_neg]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ hsChamber N
  · have hHd := (hH.contDiffAt ((isOpen_hsChamber N).mem_nhds hx)).differentiableAt (by norm_num)
    have hwd := hHd.hasFDerivAt.neg.exp
    have hd := ((hψ.differentiable (by norm_num) x).hasFDerivAt.mul hwd).fderiv
    simp only [Pi.neg_apply] at hd
    change fderiv ℝ (fun y => ψ y * Real.exp (-hsPairExpression χ y)) x = _ at hd
    rw [hd]
    simp only [add_apply, smul_apply, neg_apply, smul_eq_mul]
    ring
  · have hxs : x ∉ tsupport ψ := fun h => hx (hψU h)
    have hgs : x ∉ tsupport (fun y => ψ y * Real.exp (-hsPairExpression χ y)) :=
      fun h => hxs (tsupport_mul_subset_left h)
    rw [fderiv_of_notMem_tsupport ℝ hgs, fderiv_of_notMem_tsupport ℝ hxs,
      image_eq_zero_of_notMem_tsupport hxs]
    simp

/-- Local weighted integration by parts on the quotient. The compact test
is supported in the open fundamental strip, so no seam term occurs. -/
theorem hsGibbsLocalIntegrationByParts {N : ℕ+} {c : ℝ} (χ : HsPairPotentials N c)
    (hc : 0 < c) (φ : hsSmoothCore N) {ψ : HsEuclidean N → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ hsChamber N)
    (hψS : tsupport ψ ⊆ {x | x ⟨0, N.pos⟩ ∈ Ioo (0 : ℝ) 1}) (v : HsEuclidean N) :
    ∫ x, hsSmoothValue ψ x * inner ℝ (hsSmoothGradient φ x) v
        ∂(hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) =
      ∫ x, hsSmoothValue φ.val x *
        hsSmoothValue (fun y => ψ y * fderiv ℝ (hsPairExpression χ) y v - fderiv ℝ ψ y v) x
          ∂(hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N)) := by
  have hψF : tsupport ψ ⊆ hsFundamentalRegion N := by
    intro x hx
    exact ⟨hψU hx, (hψS hx).1.le, (hψS hx).2⟩
  have hzero (x : HsEuclidean N) (hx : x ∉ hsFundamentalRegion N) :
      ψ x = 0 ∧ fderiv ℝ ψ x = 0 := by
    have hxs : x ∉ tsupport ψ := fun h => hx (hψF h)
    exact ⟨image_eq_zero_of_notMem_tsupport hxs, fderiv_of_notMem_tsupport ℝ hxs⟩
  simp only [hsSmoothGradient, inner_gradient_left]
  change (∫ x, hsSmoothValue (fun y => ψ y * fderiv ℝ φ.val y v) x
      ∂(hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))) =
    ∫ x, hsSmoothValue (fun y => φ.val y *
      (ψ y * fderiv ℝ (hsPairExpression χ) y v - fderiv ℝ ψ y v)) x
      ∂(hsQuotientGibbsProbability χ hc : Measure (HsConfiguration N))
  rw [hsQuotientGibbsProbability_integral, hsQuotientGibbsProbability_integral]
  congr 1
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    simp only [(hzero x hx).1, zero_mul, mul_zero]),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      simp only [(hzero x hx).1, (hzero x hx).2, zero_apply,
        zero_mul, sub_zero, mul_zero])]
  convert hsLocalIntegrationByParts χ φ hψ hψc hψU v using 1 <;>
    apply integral_congr_ae <;> filter_upwards with x <;> ring

end Riesz1

end
