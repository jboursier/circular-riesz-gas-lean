/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.LogSobolevSmoothPotential
public import Riesz1.ToMathlib.Gaussian.DensityLimit

/-!
# Passing Bakry–Émery and Herbst through smooth potential approximations

These internal implications discharge the logarithmic Sobolev premise of the
Herbst theorem from `hBE`. Their remaining premise is an actual smooth potential
approximation converging against bounded continuous tests. Constructing that approximation
from a Borel log-concave density on a convex conditioning set is not proved here.
-/

public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ContDiff

namespace Riesz1.LogSobolevInternal

/-- Internal limit implication, with the LSI on every approximating measure proved using
the criterion `External.BakryEmery` rather than assumed. -/
theorem lsi_of_smooth_potential_limit (hBE : External.BakryEmery)
    {d : ℕ} (hd : 0 < d) {w : ℝ} (hw : 0 < w)
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (Vn : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (hVn : ∀ n, ContDiff ℝ ∞ (Vn n))
    (hHn : ∀ n x h, w⁻¹ * ‖h‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ (Vn n)) x h) h)
    (hlim : ∀ g : EuclideanSpace ℝ (Fin d) → ℝ, Continuous g →
      (∃ C, ∀ x, |g x| ≤ C) →
      Tendsto (fun n => ∫ x, g x ∂volume.withDensity
        (fun x => ENNReal.ofReal (Real.exp (-Vn n x) / ∫ y, Real.exp (-Vn n y)))) atTop
        (𝓝 (∫ x, g x ∂μ)))
    {q : EuclideanSpace ℝ (Fin d) → ℝ} (hq : ContDiff ℝ 1 q)
    (hqb : ∃ C, ∀ x, |q x| ≤ C) (hqd : ∃ D, ∀ x, ‖gradient q x‖ ≤ D) :
    ∃ (_ : Integrable (fun x => q x ^ 2) μ)
      (_ : Integrable (fun x => Real.negMulLog (q x ^ 2)) μ)
      (_ : Integrable (fun x => ‖gradient q x‖ ^ 2) μ),
      -(∫ x, Real.negMulLog (q x ^ 2) ∂μ) + Real.negMulLog (∫ x, q x ^ 2 ∂μ) ≤
        2 * w * ∫ x, ‖gradient q x‖ ^ 2 ∂μ := by
  obtain ⟨C, hC⟩ := hqb
  obtain ⟨D, hD⟩ := hqd
  have hD' : ∀ x, ‖fderiv ℝ q x‖ ≤ D := by
    simpa only [norm_gradient_eq_norm_fderiv] using hD
  obtain ⟨hi₁, hi₂, hi₃⟩ := test_integrable (μ := μ) hq hC hD'
  simp_rw [← norm_gradient_eq_norm_fderiv] at hi₃
  refine ⟨hi₁, hi₂, hi₃, ?_⟩
  have he := lsi_of_tendsto_integrals (w := w) hlim hq hC hD' (fun n => ?_)
  · simpa only [norm_gradient_eq_norm_fderiv] using he
  · obtain ⟨_, _, _, hLSI⟩ := logSobolev_smooth_potential_smooth hBE hd hw
      (Vn n) (hVn n) (hHn n)
    obtain ⟨_, _, _, hn⟩ := hLSI q hq ⟨C, hC⟩ ⟨D, hD⟩
    simpa only [norm_gradient_eq_norm_fderiv] using hn

/-- Internal Herbst implication for a smooth-potential limit. The observable and its
gradient are bounded on the whole ambient space, as required by the Herbst API. -/
theorem herbst_of_smooth_potential_limit (hBE : External.BakryEmery)
    {d : ℕ} (hd : 0 < d) {w : ℝ} (hw : 0 < w)
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (Vn : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (hVn : ∀ n, ContDiff ℝ ∞ (Vn n))
    (hHn : ∀ n x h, w⁻¹ * ‖h‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ (Vn n)) x h) h)
    (hlim : ∀ g : EuclideanSpace ℝ (Fin d) → ℝ, Continuous g →
      (∃ C, ∀ x, |g x| ≤ C) →
      Tendsto (fun n => ∫ x, g x ∂volume.withDensity
        (fun x => ENNReal.ofReal (Real.exp (-Vn n x) / ∫ y, Real.exp (-Vn n y)))) atTop
        (𝓝 (∫ x, g x ∂μ)))
    (F : EuclideanSpace ℝ (Fin d) → ℝ) (hF : ContDiff ℝ 1 F)
    (hFb : ∃ C, ∀ x, |F x| ≤ C) (L : ℝ) (hL : ∀ x, ‖gradient F x‖ ≤ L) (t : ℝ) :
    Real.log (∫ x, Real.exp (t * F x) ∂μ) ≤
      t * ∫ x, F x ∂μ + w / 2 * t ^ 2 * L ^ 2 := by
  apply herbst_log_mgf_le μ w hw ?_ F hF hFb L ?_ t
  · intro q hq hqb ⟨D, hD⟩
    have hqd : ∃ D, ∀ x, ‖gradient q x‖ ≤ D :=
      ⟨D, fun x => by rw [norm_gradient_eq_norm_fderiv]; exact hD x⟩
    obtain ⟨_, _, _, he⟩ := lsi_of_smooth_potential_limit hBE hd hw μ Vn hVn hHn
      hlim hq hqb hqd
    simpa only [Real.negMulLog_eq_neg, integral_neg, neg_neg,
      norm_gradient_eq_norm_fderiv, sub_eq_add_neg] using he
  · simpa only [norm_gradient_eq_norm_fderiv] using hL

end Riesz1.LogSobolevInternal

end
