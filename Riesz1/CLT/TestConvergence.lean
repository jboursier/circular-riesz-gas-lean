/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.Mollify
public import Riesz1.Frozen.BLTest
public import Riesz1.Frozen.ConvergesInLaw
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Convergence in law from `C¹` bounded-Lipschitz tests

If the integrals of every `C¹` function with `|f| ≤ 1` and `|f'| ≤ 1` converge to the integral
against the limit law, then the laws converge in law. The proof has three steps.

1. Scaling: a `C¹` function bounded by `K` with derivative bounded by `K` is a constant multiple
   of a test function, so its integrals converge.
2. Mollification: a bounded Lipschitz function is uniformly close to a `C¹` function of the same
   bound, with derivative bounded by the Lipschitz constant. Its integrals converge.
3. Portmanteau: Mathlib's characterization of weak convergence by bounded Lipschitz functions
   turns step 2 into weak convergence, and then into convergence against bounded continuous
   functions.
-/

public section

open MeasureTheory Filter Topology
open scoped NNReal

namespace Riesz1

/-- A bounded continuous function is integrable against a finite measure. -/
lemma integrable_of_continuous_abs_le {μ : Measure ℝ} [IsFiniteMeasure μ] {f : ℝ → ℝ}
    (hf : Continuous f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ fun x => by
    rw [Real.norm_eq_abs]; exact hC x)

/-- Step 1: convergence for `C¹` functions bounded by `K` with bounded derivative. -/
lemma tendsto_integral_of_contDiff {laws : ℕ → Measure ℝ} {limit : Measure ℝ}
    (h : ∀ f : ℝ → ℝ, BLTest f →
      Tendsto (fun n => ∫ x, f x ∂laws n) atTop (𝓝 (∫ x, f x ∂limit)))
    {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u) {K : ℝ} (hK : 0 < K)
    (hu0 : ∀ x, |u x| ≤ K) (hu1 : ∀ x, |deriv u x| ≤ K) :
    Tendsto (fun n => ∫ x, u x ∂laws n) atTop (𝓝 (∫ x, u x ∂limit)) := by
  have hd : ∀ x, deriv (fun y => K⁻¹ * u y) x = K⁻¹ * deriv u x := fun x =>
    congrFun (deriv_const_mul_field' K⁻¹) x
  have hf : BLTest (fun y => K⁻¹ * u y) := by
    dsimp only [BLTest]
    refine ⟨contDiff_const.mul hu, fun x => ?_, fun x => ?_⟩
    · rw [abs_mul, abs_inv, abs_of_pos hK]
      calc K⁻¹ * |u x| ≤ K⁻¹ * K := mul_le_mul_of_nonneg_left (hu0 x) (inv_nonneg.mpr hK.le)
        _ = 1 := inv_mul_cancel₀ hK.ne'
    · rw [hd, abs_mul, abs_inv, abs_of_pos hK]
      calc K⁻¹ * |deriv u x| ≤ K⁻¹ * K := mul_le_mul_of_nonneg_left (hu1 x) (inv_nonneg.mpr hK.le)
        _ = 1 := inv_mul_cancel₀ hK.ne'
  have hlim := h _ hf
  simp only [integral_const_mul] at hlim
  have key : ∀ a : ℝ, K * (K⁻¹ * a) = a := fun a => by
    rw [← mul_assoc, mul_inv_cancel₀ hK.ne', one_mul]
  simpa only [key] using hlim.const_mul K

/-- Step 2: convergence for bounded Lipschitz functions. -/
lemma tendsto_integral_of_lipschitz {laws : ℕ → Measure ℝ} {limit : Measure ℝ}
    (hlaws : ∀ n, IsProbabilityMeasure (laws n)) (hlimit : IsProbabilityMeasure limit)
    (h : ∀ f : ℝ → ℝ, BLTest f →
      Tendsto (fun n => ∫ x, f x ∂laws n) atTop (𝓝 (∫ x, f x ∂limit)))
    {g : ℝ → ℝ} {M : ℝ} {L : ℝ≥0} (hM : ∀ x, |g x| ≤ M) (hL : LipschitzWith L g) :
    Tendsto (fun n => ∫ x, g x ∂laws n) atTop (𝓝 (∫ x, g x ∂limit)) := by
  have hL0 : (0 : ℝ) ≤ L := NNReal.coe_nonneg L
  refine Metric.tendsto_nhds.mpr fun δ hδ => ?_
  -- The mollification error `ε` makes `L ε` at most `δ / 4`.
  obtain ⟨ε, hε_def⟩ : ∃ ε : ℝ, ε = δ / (4 * (L + 1)) := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hε_def]; positivity
  have hLε : (L : ℝ) * ε ≤ δ / 4 := by
    rw [hε_def, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  obtain ⟨u, hu, hu0, hu1, hgu⟩ := exists_mollified hε hM hL
  -- The `C¹` approximant is bounded by `K`, and so is its derivative.
  obtain ⟨K, hK_def⟩ : ∃ K : ℝ, K = |M| + L + 1 := ⟨_, rfl⟩
  have hK : 0 < K := by rw [hK_def]; positivity
  have hconv := tendsto_integral_of_contDiff h hu hK
    (fun x => le_trans (hu0 x) (by linarith [le_abs_self M, abs_nonneg M]))
    (fun x => le_trans (hu1 x) (by linarith [abs_nonneg M]))
  have hsmall := Metric.tendsto_nhds.mp hconv (δ / 2) (by positivity)
  -- The integrals of `g` and `u` differ by at most `L ε` under every probability measure.
  have hgu_dist : ∀ μ : Measure ℝ, IsProbabilityMeasure μ →
      dist (∫ x, g x ∂μ) (∫ x, u x ∂μ) ≤ L * ε := by
    intro μ hμ
    have := hμ
    rw [dist_eq_norm, ← integral_sub (integrable_of_continuous_abs_le hL.continuous hM)
      (integrable_of_continuous_abs_le hu.continuous hu0)]
    refine (norm_integral_le_of_norm_le_const (C := L * ε) (ae_of_all _ fun x => ?_)).trans_eq ?_
    · rw [Real.norm_eq_abs, abs_sub_comm]
      exact hgu x
    · simp
  filter_upwards [hsmall] with n hn
  have h1 := hgu_dist (laws n) (hlaws n)
  have h2 : dist (∫ x, u x ∂limit) (∫ x, g x ∂limit) ≤ L * ε := by
    rw [dist_comm]
    exact hgu_dist limit hlimit
  have h3 := dist_triangle (∫ x, g x ∂laws n) (∫ x, u x ∂laws n) (∫ x, g x ∂limit)
  have h4 := dist_triangle (∫ x, u x ∂laws n) (∫ x, u x ∂limit) (∫ x, g x ∂limit)
  linarith

/-- If the integrals of every `C¹` function with `|f| ≤ 1` and `|f'| ≤ 1` converge, then the
laws converge in law. Bounded Lipschitz functions are reached by mollification, and weak
convergence of probability measures then yields convergence against bounded continuous
functions. -/
theorem convergesInLaw_of_blTest (laws : ℕ → Measure ℝ) (limit : Measure ℝ)
    (hlaws : ∀ n, IsProbabilityMeasure (laws n)) (hlimit : IsProbabilityMeasure limit)
    (h : ∀ f : ℝ → ℝ, BLTest f →
      Tendsto (fun n => ∫ x, f x ∂laws n) atTop (𝓝 (∫ x, f x ∂limit))) :
    ConvergesInLaw laws limit := by
  -- A bounded Lipschitz function `g` is bounded by `|g 0| + C`, where `C` bounds its oscillation.
  have hbl : ∀ g : ℝ → ℝ, (∃ C : ℝ, ∀ x y, dist (g x) (g y) ≤ C) →
      (∃ L : ℝ≥0, LipschitzWith L g) →
      Tendsto (fun n => ∫ x, g x ∂laws n) atTop (𝓝 (∫ x, g x ∂limit)) := by
    rintro g ⟨C, hC⟩ ⟨L, hL⟩
    refine tendsto_integral_of_lipschitz hlaws hlimit h (M := |g 0| + C) (fun x => ?_) hL
    have hx := hC x 0
    rw [Real.dist_eq] at hx
    linarith [abs_sub_abs_le_abs_sub (g x) (g 0)]
  -- Convergence of the bounded Lipschitz integrals gives weak convergence of the probability
  -- measures, which gives convergence against bounded continuous functions.
  let μs : ℕ → ProbabilityMeasure ℝ := fun n => ⟨laws n, hlaws n⟩
  let μ : ProbabilityMeasure ℝ := ⟨limit, hlimit⟩
  have hweak : Tendsto μs atTop (𝓝 μ) :=
    MeasureTheory.tendsto_iff_forall_lipschitz_integral_tendsto.mpr fun g hC hL => hbl g hC hL
  unfold ConvergesInLaw
  exact ⟨hlaws, hlimit, fun f => ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak f⟩

end Riesz1
