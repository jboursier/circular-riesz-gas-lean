/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.BoundaryCoreUnfolding
public import Riesz1.HelfferSjostrand.QuotientChartWeakGradient
public import Riesz1.ToMathlib.PeriodizationLaplacian

/-!
# From test pairings to the distributional equation

This is the local-test bridge for the boundary core. Its pairing
condition is an internal hypothesis, to be derived from operator
orthogonality.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Function Filter Topology
open scoped ContDiff Laplacian

namespace Riesz1.Internal

/-- Vanishing pairings with the entire periodic test class imply
the distributional Schrödinger equation against arbitrary compact
Euclidean tests, including tests crossing a rotation seam. -/
theorem distributionalSchrodinger_of_source_pairings {N : ℕ+} (hN : 2 ≤ (N : ℕ))
    {W : HsCylinder N → ℝ}
    (hW : ContDiffOn ℝ ∞ (fun y : HsEuclidean N => W (QuotientAddGroup.mk y)) (hsChamber N))
    (lam : ℝ) {u : HsCylinder N → ℝ}
    (hu : MemLp (fun x : HsConfiguration N => u x.val) 2 (hsConfigurationVolume N))
    (hp : ∀ f : HsTestFunction N,
      (∫ x : HsConfiguration N,
        (-Δ f.toFun (hsLiftPoint N x) +
          (W x.val + lam) * f (hsLiftPoint N x)) * u x.val ∂hsConfigurationVolume N) = 0) :
    IsDistributionalSchrodingerSolution (hsChamber N)
      (fun y => W (QuotientAddGroup.mk y)) lam (fun y => u (QuotientAddGroup.mk y)) := by
  let w : HsEuclidean N → ℝ := fun y => W (QuotientAddGroup.mk y)
  let v : HsEuclidean N → ℝ := fun y => u (QuotientAddGroup.mk y)
  have hvl := locallySquareIntegrableOn_quotient_mk hu
  have hvi : LocallyIntegrableOn v (hsChamber N) := hvl.locallyIntegrableOn (isOpen_hsChamber N)
  have hwv : LocallyIntegrableOn (fun y => (w y + lam) • v y) (hsChamber N) :=
    (hvl.smul_continuousOn (hW.continuousOn.add continuousOn_const)).locallyIntegrableOn
      (isOpen_hsChamber N)
  refine ⟨hvi, hwv, ?_⟩
  intro φ hφ hφc hφU
  let q : HsEuclidean N → ℝ := fun y => φ y * (w y + lam) - Δ φ y
  have hqc : HasCompactSupport q := hφc.mul_right.sub (hasCompactSupport_laplacian hφc)
  have hqU : tsupport q ⊆ hsChamber N :=
    ((tsupport_sub _ _).trans (union_subset tsupport_mul_subset_left
      (tsupport_laplacian_subset φ))).trans hφU
  have hq : Continuous q :=
    (WeightedSobolev.continuous_cutoff_mul (isOpen_hsChamber N) hφ.continuous hφU
      (hW.continuousOn.add continuousOn_const)).sub (contDiff_laplacian hφ).continuous
  let P := hsTestFunctionOfCompact hN hφ hφc hφU
  have hwp (k : ℤ) (y : HsEuclidean N) :
      w (y + (k : ℝ) • hsRotationVector N) = w y := by
    rw [← hsTranslate_eq_add_rotation]
    exact congrArg W (Internal.hs_quotient_mk_translate k y)
  have hqp (y : HsEuclidean N) :
      vectorPeriodize (hsRotationVector N) (hsRotationVector_ne_zero N) q hqc y =
        P y * (w y + lam) - Δ P.toFun y := by
    rw [show P.toFun = vectorPeriodize (hsRotationVector N) (hsRotationVector_ne_zero N) φ hφc
      from rfl, laplacian_vectorPeriodize (hsRotationVector_ne_zero N) hφ hφc]
    unfold vectorPeriodize
    simp only [q, hwp]
    have hfin : HasFiniteSupport (fun k : ℤ =>
        φ (y + (k : ℝ) • hsRotationVector N) * (w y + lam)) := by
      simpa only [hwp] using (vectorPeriodize_finite_support (hsRotationVector_ne_zero N)
        (show HasCompactSupport (fun z => φ z * (w z + lam)) from hφc.mul_right) y)
    rw [finsum_sub_distrib hfin
      (vectorPeriodize_finite_support (hsRotationVector_ne_zero N)
        (hasCompactSupport_laplacian hφc) y), finsum_mul]
  have hvp (k : ℤ) (y : HsEuclidean N) : v (hsTranslate (k : ℝ) y) = v y :=
    congrArg u (Internal.hs_quotient_mk_translate k y)
  have he := hsVolumeIntegral_periodized_test_locallyIntegrable hq hqc hqU hvi hvp
  have hz : (∫ y, q y * v y) = 0 := by
    rw [← he]
    convert hp P using 1
    apply integral_congr_ae
    filter_upwards with x
    have hx : (QuotientAddGroup.mk (hsLiftPoint N x) : HsCylinder N) = x.val :=
      congrArg Subtype.val (hsChamberProjection_liftPoint x)
    simp only [hsSmoothValue, hqp, w, v, hx]
    ring
  have hi : Integrable (fun y => φ y • ((w y + lam) • v y)) :=
    integrable_smul_of_compact_interior hwv hφ.continuous hφc hφU
  have hj : Integrable (fun y => (Δ φ) y • v y) :=
    integrable_smul_of_compact_interior hvi (contDiff_laplacian hφ).continuous
      (hasCompactSupport_laplacian hφc) ((tsupport_laplacian_subset φ).trans hφU)
  have heq : (fun y => q y * v y) =
      (fun y => φ y • ((w y + lam) • v y) - (Δ φ) y • v y) := by
    funext y
    simp only [q, smul_eq_mul]
    ring
  rw [heq, integral_sub hi hj] at hz
  exact sub_eq_zero.mp hz

end Riesz1.Internal
