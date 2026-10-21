/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.LogSobolevConditioning
public import Riesz1.HelfferSjostrand.LogSobolevConditioningLipschitz
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Herbst bound with bounds imposed only on the conditioning domain

The derivative bound on a convex set makes the observable Lipschitz there. Extend it with
the same Lipschitz constant, truncate the extension at its bounds on the set, then mollify.
The conditioning LSI discharges the Herbst premise. This proves the bounded-observable
checkpoint. Unbounded observables and Sobolev tests are not asserted here.
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ContDiff

namespace Riesz1

/-- Herbst for a log-concave Gaussian density, with both observable bounds imposed only on
`Ω`. No smoothness or derivative bound outside `Ω` is required beyond the stated C¹ class. -/
theorem logSobolev_conditioning_density_herbst_bounded (hBE : External.BakryEmery)
    {d : ℕ} (hd : 0 < d) {w : ℝ} (hw : 0 < w)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : Convex ℝ Ω) (hΩm : MeasurableSet Ω)
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf0 : ∀ x ∈ Ω, 0 ≤ f x)
    (hlog : ∀ x ∈ Ω, ∀ y ∈ Ω, ∀ t : ℝ, 0 < t → t < 1 →
      f x ^ t * f y ^ (1 - t) ≤ f (t • x + (1 - t) • y))
    {c : ℝ} (hc : 0 < c) (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure ν]
    (hν : ν = volume.withDensity (fun x => ENNReal.ofReal
      (c * Ω.indicator (fun y => f y * Real.exp (-((2*w)⁻¹ * ‖y‖^2))) x)))
    {F : EuclideanSpace ℝ (Fin d) → ℝ} (hF : ContDiff ℝ 1 F)
    (hFb : ∃ C, ∀ x ∈ Ω, |F x| ≤ C) {L : ℝ} (hL : ∀ x ∈ Ω, ‖gradient F x‖ ≤ L)
    (t : ℝ) :
    Integrable F ν ∧ Integrable (fun x => Real.exp (t * F x)) ν ∧
      Real.log (∫ x, Real.exp (t * F x) ∂ν) ≤
        t * ∫ x, F x ∂ν + w/2 * t^2 * L^2 := by
  classical
  have hν' : ν = (volume.restrict Ω).withDensity
      (fun x => ENNReal.ofReal (c * (f x * Real.exp (-((2*w)⁻¹ * ‖x‖^2))))) := by
    rw [hν, ← withDensity_indicator hΩm]
    congr 1
    funext x
    by_cases hx : x ∈ Ω <;> simp [hx]
  have hΩae : ∀ᵐ x ∂ν, x ∈ Ω := by
    rw [hν']
    exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hΩm)
  obtain ⟨x₀, hx₀⟩ := hΩae.exists
  obtain ⟨C, hC⟩ := hFb
  have hC0 : 0 ≤ C := (abs_nonneg (F x₀)).trans (hC x₀ hx₀)
  have hL0 : 0 ≤ L := (norm_nonneg (gradient F x₀)).trans (hL x₀ hx₀)
  let K : ℝ≥0 := ⟨L, hL0⟩
  have hFL : LipschitzOnWith K F Ω := by
    apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun x _ => hF.differentiable one_ne_zero x) _ hΩ
    intro x hx
    change ‖fderiv ℝ F x‖₊ ≤ (⟨L, hL0⟩ : ℝ≥0)
    apply NNReal.coe_le_coe.mp
    rw [coe_nnnorm]
    change ‖fderiv ℝ F x‖ ≤ L
    simpa only [LogSobolevInternal.norm_gradient_eq_norm_fderiv] using hL x hx
  obtain ⟨G₀, hG₀, heq⟩ := hFL.extend_real
  let G := fun x => max (-C) (min C (G₀ x))
  have hG : LipschitzWith K G := (hG₀.const_min C).const_max (-C)
  have hGb : ∀ x, |G x| ≤ C := by
    intro x
    rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hFG : F =ᵐ[ν] G := by
    filter_upwards [hΩae] with x hx
    dsimp [G]
    rw [← heq hx, min_eq_right (abs_le.mp (hC x hx)).2,
      max_eq_right (abs_le.mp (hC x hx)).1]
  have hE : (fun x => Real.exp (t * F x)) =ᵐ[ν] (fun x => Real.exp (t * G x)) :=
    hFG.mono (fun _ hx => congrArg (fun r => Real.exp (t * r)) hx)
  refine ⟨(herbst_integrable_of_bounded hG.continuous hGb).congr hFG.symm,
    (herbst_integrable_exp hG.continuous hGb t).congr hE.symm, ?_⟩
  rw [integral_congr_ae hFG, integral_congr_ae hE]
  apply LogSobolevInternal.herbst_bounded_lipschitz_of_lsi ν hw _ hG hGb t
  intro q hq hqb ⟨D, hD⟩
  obtain ⟨_, _, _, he⟩ := logSobolev_conditioning_density_smooth hBE hd hw hΩ hf0 hlog hc ν hν
    hq hqb ⟨D, fun x => by rw [LogSobolevInternal.norm_gradient_eq_norm_fderiv]; exact hD x⟩
  simpa only [Real.negMulLog_eq_neg, integral_neg, neg_neg,
    LogSobolevInternal.norm_gradient_eq_norm_fderiv, sub_eq_add_neg] using he

/-- **Herbst under convex conditioning, bounded observable.** Both the value bound and the
bound `‖∇F‖ ≤ L` are needed only on `Ω`, and every real tilt `t` is allowed. -/
theorem logSobolev_conditioning_herbst_bounded (hBE : External.BakryEmery)
    {d : ℕ} (hd : 0 < d) {w : ℝ} (hw : 0 < w)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : Convex ℝ Ω) (hΩm : MeasurableSet Ω)
    (hΩpos : 0 < ∫ x in Ω, Real.exp (-((2*w)⁻¹ * ‖x‖^2)))
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f) (hf0 : ∀ x ∈ Ω, 0 ≤ f x)
    (hlog : ∀ x ∈ Ω, ∀ y ∈ Ω, ∀ t : ℝ, 0 < t → t < 1 →
      f x ^ t * f y ^ (1 - t) ≤ f (t • x + (1 - t) • y))
    (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure ν]
    (hν : ν = ((volume.restrict Ω).withDensity (fun x => ENNReal.ofReal
      (Real.exp (-((2*w)⁻¹ * ‖x‖^2)) / ∫ y in Ω, Real.exp (-((2*w)⁻¹ * ‖y‖^2))))).withDensity
        (fun x => ENNReal.ofReal (f x)))
    {F : EuclideanSpace ℝ (Fin d) → ℝ} (hF : ContDiff ℝ 1 F)
    (hFb : ∃ C, ∀ x ∈ Ω, |F x| ≤ C) {L : ℝ} (hL : ∀ x ∈ Ω, ‖gradient F x‖ ≤ L)
    (t : ℝ) :
    Integrable F ν ∧ Integrable (fun x => Real.exp (t * F x)) ν ∧
      Real.log (∫ x, Real.exp (t * F x) ∂ν) ≤
        t * ∫ x, F x ∂ν + w/2 * t^2 * L^2 := by
  exact logSobolev_conditioning_density_herbst_bounded hBE hd hw hΩ hΩm hf0 hlog
    (inv_pos.mpr hΩpos) ν (hν.trans (LogSobolevInternal.conditioned_density_eq hΩm hf hΩpos))
    hF hFb hL t

end Riesz1

end
