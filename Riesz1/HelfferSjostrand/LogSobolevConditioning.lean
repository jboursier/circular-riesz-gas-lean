/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.LogSobolevConditioningSupport
public import Riesz1.HelfferSjostrand.LogSobolevLimit

/-!
# Logarithmic Sobolev inequality under convex conditioning

For a probability with a log-concave density relative to a Gaussian conditioned on a convex
Borel set, Bakry–Émery extends to globally bounded C¹ tests with bounded gradient. The
smooth-potential approximations, their curvature and convergence are constructed from the
density. The density may vanish on any part of the conditioning set.

The Gaussian is written using its Lebesgue density, so its ambient normalizing constant
cancels when conditioning. The positive integral hypothesis is positive Gaussian mass of
the conditioning set. No Sobolev completion is asserted in this file.
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Riesz1

/-- The C¹ log-Sobolev inequality for an arbitrary normalized log-concave Gaussian density.
The positive scalar permits either normalized or unnormalized Gaussian reference densities. -/
theorem logSobolev_conditioning_density_smooth (hBE : External.BakryEmery)
    {d : ℕ} (hd : 0 < d) {w : ℝ} (hw : 0 < w)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : Convex ℝ Ω)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf0 : ∀ x ∈ Ω, 0 ≤ f x)
    (hlog : ∀ x ∈ Ω, ∀ y ∈ Ω, ∀ t : ℝ, 0 < t → t < 1 →
      f x ^ t * f y ^ (1 - t) ≤ f (t • x + (1 - t) • y))
    {c : ℝ} (hc : 0 < c) (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure ν]
    (hν : ν = volume.withDensity (fun x => ENNReal.ofReal
      (c * Ω.indicator (fun y => f y * Real.exp (-((2*w)⁻¹ * ‖y‖^2))) x)))
    {q : EuclideanSpace ℝ (Fin d) → ℝ} (hq : ContDiff ℝ 1 q)
    (hqb : ∃ C, ∀ x, |q x| ≤ C) (hqd : ∃ D, ∀ x, ‖gradient q x‖ ≤ D) :
    ∃ (_ : Integrable (fun x => q x ^ 2) ν)
      (_ : Integrable (fun x => Real.negMulLog (q x ^ 2)) ν)
      (_ : Integrable (fun x => ‖gradient q x‖ ^ 2) ν),
      -(∫ x, Real.negMulLog (q x ^ 2) ∂ν) + Real.negMulLog (∫ x, q x ^ 2 ∂ν) ≤
        2 * w * ∫ x, ‖gradient q x‖ ^ 2 ∂ν := by
  obtain ⟨Vn, hVn, hHn, hlim⟩ :=
    LogSobolevInternal.logConcave_gaussian_approximation hw hΩ hf0 hlog hc ν hν
  exact LogSobolevInternal.lsi_of_smooth_potential_limit hBE hd hw ν Vn hVn hHn hlim hq hqb hqd

namespace LogSobolevInternal

/-- Expands a conditioned Gaussian density and its log-concave perturbation into a single
Lebesgue density. This is an identity of the given measures, not a convergence premise. -/
lemma conditioned_density_eq {d : ℕ} {w : ℝ}
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩm : MeasurableSet Ω)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f)
    (hZ : 0 < ∫ x in Ω, Real.exp (-((2*w)⁻¹ * ‖x‖^2))) :
    (((volume.restrict Ω).withDensity (fun x => ENNReal.ofReal
      (Real.exp (-((2*w)⁻¹ * ‖x‖^2)) / ∫ y in Ω, Real.exp (-((2*w)⁻¹ * ‖y‖^2))))).withDensity (fun x => ENNReal.ofReal (f x))) =
      volume.withDensity (fun x => ENNReal.ofReal
        ((∫ y in Ω, Real.exp (-((2*w)⁻¹ * ‖y‖^2)))⁻¹ *
          Ω.indicator (fun y => f y * Real.exp (-((2*w)⁻¹ * ‖y‖^2))) x)) := by
  classical
  have hg : Measurable (fun x : EuclideanSpace ℝ (Fin d) => ENNReal.ofReal
      (Real.exp (-((2*w)⁻¹ * ‖x‖^2)) / ∫ y in Ω, Real.exp (-((2*w)⁻¹ * ‖y‖^2)))) := by
    fun_prop
  rw [← withDensity_mul _ hg hf.ennreal_ofReal, ← withDensity_indicator hΩm]
  congr 1
  funext x
  by_cases hx : x ∈ Ω
  · simp only [indicator_of_mem hx, Pi.mul_apply]
    rw [← ENNReal.ofReal_mul (div_nonneg (Real.exp_pos _).le hZ.le)]
    congr 1
    ring
  · simp only [indicator_of_notMem hx, mul_zero, ENNReal.ofReal_zero]

end LogSobolevInternal

/-- **Convex conditioning, C¹ tests.** Let `ν = f γΩ`, where `γΩ` is the centered Gaussian
of covariance `w I` conditioned on the convex Borel set `Ω`. Then `Entν(q²) ≤ 2w ∫ ‖∇q‖²`.
The Borel density is log-concave on all of `Ω`, including its zero values. Its ambient
representative outside `Ω` has no effect on either measure or the assumptions on the density. -/
theorem logSobolev_conditioning_smooth (hBE : External.BakryEmery)
    {d : ℕ} (hd : 0 < d) {w : ℝ} (hw : 0 < w)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : Convex ℝ Ω) (hΩm : MeasurableSet Ω)
    (hΩpos : 0 < ∫ x in Ω, Real.exp (-((2*w)⁻¹ * ‖x‖^2)))
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f) (hf0 : ∀ x ∈ Ω, 0 ≤ f x)
    (hlog : ∀ x ∈ Ω, ∀ y ∈ Ω, ∀ t : ℝ, 0 < t → t < 1 →
      f x ^ t * f y ^ (1 - t) ≤ f (t • x + (1 - t) • y))
    (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure ν]
    (hν : ν = ((volume.restrict Ω).withDensity (fun x => ENNReal.ofReal
      (Real.exp (-((2*w)⁻¹ * ‖x‖^2)) / ∫ y in Ω, Real.exp (-((2*w)⁻¹ * ‖y‖^2))))).withDensity (fun x => ENNReal.ofReal (f x)))
    {q : EuclideanSpace ℝ (Fin d) → ℝ} (hq : ContDiff ℝ 1 q)
    (hqb : ∃ C, ∀ x, |q x| ≤ C) (hqd : ∃ D, ∀ x, ‖gradient q x‖ ≤ D) :
    ∃ (_ : Integrable (fun x => q x ^ 2) ν)
      (_ : Integrable (fun x => Real.negMulLog (q x ^ 2)) ν)
      (_ : Integrable (fun x => ‖gradient q x‖ ^ 2) ν),
      -(∫ x, Real.negMulLog (q x ^ 2) ∂ν) + Real.negMulLog (∫ x, q x ^ 2 ∂ν) ≤
        2 * w * ∫ x, ‖gradient q x‖ ^ 2 ∂ν := by
  apply logSobolev_conditioning_density_smooth hBE hd hw hΩ hf0 hlog (inv_pos.mpr hΩpos) ν
    (hν.trans (LogSobolevInternal.conditioned_density_eq hΩm hf hΩpos)) hq hqb hqd

end Riesz1

end
