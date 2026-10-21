/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.HelfferSjostrand.LogSobolevHerbstH1Unbounded
public import Riesz1.ToMathlib.LogConcave.PrekopaContinuity
public import Mathlib.MeasureTheory.Measure.Tilted

/-!
# Concentration of Lipschitz functions under strongly convex potentials

The potential is finite on a bounded open convex domain. Its convex
residual need not be smooth. Normalization and integrability are proved.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology NNReal

namespace Riesz1.Internal

/-- The Lipschitz version of the Gaussian convex-conditioning Herbst bound.
The only external input is the Bakry–Émery criterion `External.BakryEmery`,
taken as the hypothesis `hBE`. -/
theorem convex_potential_lipschitz_concentration (hBE : External.BakryEmery)
    {d : ℕ} {U : Set (EuclideanSpace ℝ (Fin d))}
    (ho : IsOpen U) (hc : Convex ℝ U) (hbd : Bornology.IsBounded U) (hne : U.Nonempty)
    {V : EuclideanSpace ℝ (Fin d) → ℝ} {κ : ℝ} (hκ : 0 < κ)
    (hB : ConvexOn ℝ U (fun x => V x - κ / 2 * ‖x‖ ^ 2))
    {F : EuclideanSpace ℝ (Fin d) → ℝ}
    {L : ℝ≥0} (hFL : LipschitzOnWith L F U)
    (t : ℝ) :
    IsProbabilityMeasure ((volume.restrict U).tilted (fun x => -V x)) ∧
      Integrable F ((volume.restrict U).tilted (fun x => -V x)) ∧
      Integrable (fun x => Real.exp (t * F x)) ((volume.restrict U).tilted (fun x => -V x)) ∧
      Real.log (∫ x, Real.exp (t * F x) ∂((volume.restrict U).tilted (fun x => -V x))) ≤
        t * ∫ x, F x ∂((volume.restrict U).tilted (fun x => -V x)) + t ^ 2 * (L : ℝ) ^ 2 / (2 * κ) := by
  let B : EuclideanSpace ℝ (Fin d) → ℝ := fun x => V x - κ / 2 * ‖x‖ ^ 2
  have hBc : ContinuousOn B U := by
    have h := hB.continuousOn_interior
    rwa [ho.interior_eq] at h
  have hVc : ContinuousOn V U := by
    convert hBc.add (show ContinuousOn (fun x : EuclideanSpace ℝ (Fin d) => κ / 2 * ‖x‖ ^ 2) U by fun_prop) using 1
    funext x
    exact (sub_add_cancel (V x) (κ / 2 * ‖x‖ ^ 2)).symm
  obtain ⟨b, hb⟩ := exists_lower_bound_of_convexOn ho hbd hB
  have hVb : ∀ x ∈ U, b ≤ V x := by
    intro x hx
    have := hb x hx
    have hq : 0 ≤ κ / 2 * ‖x‖ ^ 2 := mul_nonneg (by positivity) (sq_nonneg _)
    linarith
  have hI : IntegrableOn (fun x => Real.exp (-V x)) U := by
    refine Integrable.mono' (g := fun _ => Real.exp (-b))
      (integrableOn_const (hC := by simp) hbd.measure_lt_top.ne)
      ((Real.continuous_exp.comp_continuousOn hVc.neg).aestronglyMeasurable ho.measurableSet) ?_
    filter_upwards [ae_restrict_mem ho.measurableSet] with x hx
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_exp.mpr (neg_le_neg (hVb x hx))
  have : NeZero (volume.restrict U) :=
    ⟨fun hz => (ho.measure_pos volume hne).ne' (Measure.restrict_eq_zero.mp hz)⟩
  have hZ : 0 < ∫ x in U, Real.exp (-V x) := integral_exp_pos hI
  have hp : IsProbabilityMeasure ((volume.restrict U).tilted (fun x => -V x)) :=
    isProbabilityMeasure_tilted hI
  have := hp
  by_cases hd : 0 < d
  swap
  · have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
    subst d
    have hFc : F = fun _ => F 0 := funext fun x => congrArg F (Subsingleton.elim x 0)
    refine ⟨hp, ?_, ?_, ?_⟩
    · rw [hFc]
      exact integrable_const _
    · rw [hFc]
      exact integrable_const _
    · rw [hFc]
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, Real.log_exp]
      exact le_add_of_nonneg_right (div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
        (by positivity))
  let f : EuclideanSpace ℝ (Fin d) → ℝ := U.indicator (fun x => Real.exp (-B x))
  have hfm : Measurable f := measurable_indicator_of_continuousOn ho
    (Real.continuous_exp.comp_continuousOn hBc.neg)
  have hfU (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ U) : f x = Real.exp (-B x) :=
    indicator_of_mem hx _
  have hlog : ∀ x ∈ U, ∀ y ∈ U, ∀ s : ℝ, 0 < s → s < 1 →
      f x ^ s * f y ^ (1 - s) ≤ f (s • x + (1 - s) • y) := by
    intro x hx y hy s hs0 hs1
    rw [hfU x hx, hfU y hy,
      hfU _ (hc hx hy hs0.le (by linarith) (by ring)), ← Real.exp_mul, ← Real.exp_mul,
      ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := hB.2 hx hy hs0.le (show 0 ≤ 1 - s by linarith) (by ring : s + (1 - s) = 1)
    change -(V x - κ / 2 * ‖x‖ ^ 2) * s + -(V y - κ / 2 * ‖y‖ ^ 2) * (1 - s) ≤
      -(V (s • x + (1 - s) • y) - κ / 2 * ‖s • x + (1 - s) • y‖ ^ 2)
    simp only [smul_eq_mul] at h
    nlinarith
  have hk : (2 * κ⁻¹)⁻¹ = κ / 2 := by field_simp
  have hν : (volume.restrict U).tilted (fun x => -V x) =
      volume.withDensity (fun x => ENNReal.ofReal
        ((∫ y in U, Real.exp (-V y))⁻¹ * U.indicator
          (fun y => f y * Real.exp (-((2 * κ⁻¹)⁻¹ * ‖y‖ ^ 2))) x)) := by
    rw [Measure.tilted, ← withDensity_indicator ho.measurableSet]
    congr 1
    funext x
    by_cases hx : x ∈ U
    · rw [indicator_of_mem hx, indicator_of_mem hx, hfU x hx, hk]
      congr 1
      rw [← Real.exp_add]
      have he : -B x + -(κ / 2 * ‖x‖ ^ 2) = -V x := by dsimp [B]; ring
      rw [he]
      ring
    · simp only [indicator_of_notMem hx, mul_zero, ENNReal.ofReal_zero]
  have h := logSobolev_conditioning_density_herbst_lipschitz hBE hd (inv_pos.mpr hκ) hc ho.measurableSet hfm
    (fun x hx => by rw [hfU x hx]; exact (Real.exp_pos _).le) hlog (inv_pos.mpr hZ)
    ((volume.restrict U).tilted (fun x => -V x)) hν
    hFL t
  refine ⟨hp, h.1, h.2.1, ?_⟩
  convert h.2.2 using 1
  ring

end Riesz1.Internal

end
