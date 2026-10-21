/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Bounded smooth approximations of scalar derivatives

Mollification of a bounded continuous scalar function preserves a uniform bound
and converges at every point. Primitives give simultaneous approximation of a
`C¹` map and its derivative, with the origin fixed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ContDiff

namespace Riesz1.WeightedSobolev

/-- Bounded continuous scalar functions admit uniformly bounded smooth pointwise approximations. -/
theorem exists_smooth_bounded_pointwise {d : ℝ → ℝ} (hd : Continuous d)
    {C : ℝ} (hb : ∀ r, ‖d r‖ ≤ C) :
    ∃ g : ℕ → ℝ → ℝ, (∀ k, ContDiff ℝ ∞ (g k)) ∧
      (∀ k r, ‖g k r‖ ≤ 3 * C) ∧
      ∀ r, Tendsto (fun k => g k r) atTop (𝓝 (d r)) := by
  have hε (k : ℕ) : 0 < (1 : ℝ) / (k + 1) := by positivity
  choose g hg hga using fun k =>
    hd.exists_contDiff_dist_le_of_forall_mem_ball_dist_le (hε k)
  refine ⟨g, hg, ?_, ?_⟩
  · intro k r
    have hh : dist (g k r) (d r) ≤ 2 * C := hga k r _ (fun x _ => by
      rw [dist_eq_norm]
      exact (norm_sub_le _ _).trans (by linarith [hb x, hb r]))
    calc
      ‖g k r‖ = ‖(g k r - d r) + d r‖ := by rw [sub_add_cancel]
      _ ≤ ‖g k r - d r‖ + ‖d r‖ := norm_add_le _ _
      _ ≤ 3 * C := by rw [← dist_eq_norm]; linarith [hb r]
  · intro r
    apply Metric.tendsto_nhds.mpr
    intro ε hε'
    obtain ⟨δ, hδ, hdδ⟩ := Metric.continuousAt_iff.mp hd.continuousAt (ε / 2) (half_pos hε')
    have he := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (gt_mem_nhds hδ)
    filter_upwards [he] with k hk
    apply (hga k r (ε / 2) ?_).trans_lt (half_lt_self hε')
    intro x hx
    exact (hdδ ((Metric.mem_ball.mp hx).trans hk)).le

/-- A `C¹` map fixing zero admits smooth approximations fixing zero, with
uniformly bounded derivatives and pointwise convergence of values and derivatives. -/
theorem exists_smooth_approximation_C1 {T : ℝ → ℝ} (hT : ContDiff ℝ 1 T)
    (h0 : T 0 = 0) {C : ℝ} (hb : ∀ r, ‖deriv T r‖ ≤ C) :
    ∃ S : ℕ → ℝ → ℝ, (∀ k, ContDiff ℝ ∞ (S k)) ∧ (∀ k, S k 0 = 0) ∧
      (∀ k r, ‖deriv (S k) r‖ ≤ 3 * C) ∧
      (∀ r, Tendsto (fun k => S k r) atTop (𝓝 (T r))) ∧
      ∀ r, Tendsto (fun k => deriv (S k) r) atTop (𝓝 (deriv T r)) := by
  obtain ⟨g, hg, hgb, hgl⟩ := exists_smooth_bounded_pointwise hT.continuous_deriv_one hb
  let S : ℕ → ℝ → ℝ := fun k r => ∫ t in (0 : ℝ)..r, g k t
  have hSd k r : HasDerivAt (S k) (g k r) r :=
    ((hg k).continuous.integral_hasStrictDerivAt 0 r).hasDerivAt
  have hder k : deriv (S k) = g k := funext fun r => (hSd k r).deriv
  refine ⟨S, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    exact contDiff_infty_iff_deriv.mpr ⟨fun r => (hSd k r).differentiableAt,
      (hder k).symm ▸ hg k⟩
  · intro k
    exact intervalIntegral.integral_same
  · intro k r
    rw [hder]
    exact hgb k r
  · intro r
    have hi (a b : ℝ) : Tendsto (fun k => ∫ t in Ioc a b, g k t) atTop
        (𝓝 (∫ t in Ioc a b, deriv T t)) := by
      apply tendsto_integral_of_dominated_convergence (fun _ => 3 * C)
        (fun k => (hg k).continuous.aestronglyMeasurable)
        (integrable_const _)
        (fun k => Eventually.of_forall fun t => hgb k t)
        (Eventually.of_forall hgl)
    have he : (∫ t in (0 : ℝ)..r, deriv T t) = T r := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => (hT.differentiable (by norm_num) x).hasDerivAt)
        (hT.continuous_deriv_one.intervalIntegrable _ _), h0, sub_zero]
    change Tendsto (fun k => S k r) atTop (𝓝 (T r))
    rw [← he]
    exact (hi 0 r).sub (hi r 0)
  · simpa only [hder] using hgl

end Riesz1.WeightedSobolev

end
