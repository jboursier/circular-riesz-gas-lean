/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.WeightedSobolev.ScalarApproximation
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Smooth approximations for finitely piecewise C¹ scalar maps

Mollification of a bounded locally integrable scalar function preserves a uniform
bound and converges at continuity points. Primitives approximate a Lipschitz map
and its derivative away from finitely many break values, fixing the origin.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ContDiff NNReal

namespace Riesz1.WeightedSobolev

/-- Bounded locally integrable functions admit smooth approximations converging at every continuity point. -/
theorem exists_smooth_bounded_at_continuity {d : ℝ → ℝ} (hd : LocallyIntegrable d volume)
    {C : ℝ} (hb : ∀ r, ‖d r‖ ≤ C) :
    ∃ g : ℕ → ℝ → ℝ, (∀ k, ContDiff ℝ ∞ (g k)) ∧
      (∀ k r, ‖g k r‖ ≤ 3 * C) ∧
      ∀ r, ContinuousAt d r → Tendsto (fun k => g k r) atTop (𝓝 (d r)) := by
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
  · intro r hdr
    apply Metric.tendsto_nhds.mpr
    intro ε hε'
    obtain ⟨δ, hδ, hdδ⟩ := Metric.continuousAt_iff.mp hdr (ε / 2) (half_pos hε')
    have he := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (gt_mem_nhds hδ)
    filter_upwards [he] with k hk
    apply (hga k r (ε / 2) ?_).trans_lt (half_lt_self hε')
    intro x hx
    exact (hdδ ((Metric.mem_ball.mp hx).trans hk)).le

/-- Simultaneous smooth approximation of a Lipschitz map and of its derivative
away from a finite set of break values. -/
theorem exists_smooth_approximation_piecewise {T : ℝ → ℝ} {C : ℝ≥0}
    (hT : LipschitzWith C T) (h0 : T 0 = 0) {B : Set ℝ} (hB : B.Finite)
    (hTC : ContDiffOn ℝ 1 T Bᶜ) :
    ∃ S : ℕ → ℝ → ℝ, (∀ k, ContDiff ℝ ∞ (S k)) ∧ (∀ k, S k 0 = 0) ∧
      (∀ k r, ‖deriv (S k) r‖ ≤ 3 * (C : ℝ)) ∧
      (∀ r, Tendsto (fun k => S k r) atTop (𝓝 (T r))) ∧
      ∀ r, r ∉ B → Tendsto (fun k => deriv (S k) r) atTop (𝓝 (deriv T r)) := by
  have hb r : ‖deriv T r‖ ≤ (C : ℝ) := norm_deriv_le_of_lipschitz hT
  have hdi : LocallyIntegrable (deriv T) volume :=
    (continuous_const.locallyIntegrable (f := fun _ : ℝ => (C : ℝ))).mono
      (aestronglyMeasurable_deriv T volume) (Eventually.of_forall fun r => by
        exact (hb r).trans (by rw [Real.norm_eq_abs]; exact le_abs_self _))
  obtain ⟨g, hg, hgb, hgl⟩ := exists_smooth_bounded_at_continuity hdi hb
  have hdc r (hr : r ∉ B) : ContinuousAt (deriv T) r :=
    (hTC.continuousOn_deriv_of_isOpen hB.isClosed.isOpen_compl (by norm_num)).continuousAt
      (hB.isClosed.isOpen_compl.mem_nhds hr)
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
    have hl : ∀ᵐ t ∂volume, Tendsto (fun k => g k t) atTop (𝓝 (deriv T t)) := by
      filter_upwards [hB.countable.ae_notMem volume] with t ht
      exact hgl t (hdc t ht)
    have hi (a b : ℝ) : Tendsto (fun k => ∫ t in Ioc a b, g k t) atTop
        (𝓝 (∫ t in Ioc a b, deriv T t)) := by
      exact tendsto_integral_of_dominated_convergence (fun _ => 3 * (C : ℝ))
        (fun k => (hg k).continuous.aestronglyMeasurable) (integrable_const _)
        (fun k => Eventually.of_forall fun t => hgb k t) (ae_restrict_of_ae hl)
    have he : (∫ t in (0 : ℝ)..r, deriv T t) = T r := by
      rw [hT.lipschitzOnWith.absolutelyContinuousOnInterval.integral_deriv_eq_sub, h0, sub_zero]
    change Tendsto (fun k => S k r) atTop (𝓝 (T r))
    rw [← he]
    exact (hi 0 r).sub (hi r 0)
  · intro r hr
    simpa only [hder] using hgl r (hdc r hr)

end Riesz1.WeightedSobolev

end
