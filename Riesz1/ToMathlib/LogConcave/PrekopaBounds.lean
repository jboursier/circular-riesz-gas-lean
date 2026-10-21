/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Lower bounds for finite convex functions on bounded open convex sets

A finite convex function on a bounded open convex set is bounded below. The proof
compares a point with its reflection through a fixed interior point, and uses the
continuity of the function on a small closed ball around that point.
-/

@[expose] public section

noncomputable section

open Set Metric

namespace Riesz1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A finite convex function on a bounded open convex set is bounded below by a constant. -/
theorem exists_lower_bound_of_convexOn {Q : Set E} (hQo : IsOpen Q)
    (hQb : Bornology.IsBounded Q) {f : E → ℝ} (hf : ConvexOn ℝ Q f) :
    ∃ c : ℝ, ∀ p ∈ Q, c ≤ f p := by
  rcases Q.eq_empty_or_nonempty with rfl | ⟨p0, hp0⟩
  · exact ⟨0, fun p hp => hp.elim⟩
  -- Choose a closed ball around `p0` inside `Q`, and a bound `R` for `Q`.
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hQo p0 hp0
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall p0).mp hQb
  set ρ : ℝ := ε / 2 with hρ_def
  have hρ : 0 < ρ := by positivity
  have hclosed : closedBall p0 ρ ⊆ Q :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  -- The function is continuous on `Q`, hence bounded above on the compact ball.
  have hcont : ContinuousOn f Q := by
    have h := hf.continuousOn_interior
    rwa [hQo.interior_eq] at h
  obtain ⟨m, hm, hmax⟩ := (isCompact_closedBall p0 ρ).exists_isMaxOn
    ⟨p0, Metric.mem_closedBall_self hρ.le⟩ (hcont.mono hclosed)
  set M : ℝ := f m with hM_def
  set t : ℝ := ρ / (R + 1) with ht_def
  have hR1 : 0 < R + 1 := by
    have hpR := hR hp0
    have : 0 ≤ R := le_trans (dist_nonneg) hpR
    linarith
  have ht : 0 < t := div_pos hρ hR1
  refine ⟨((1 + t) * f p0 - M) / t, fun p hp => ?_⟩
  -- The reflected point `q = (1 + t) p0 - t p` stays in the ball of radius `ρ`.
  set q : E := (1 + t) • p0 - t • p with hq_def
  have hdist : dist q p0 ≤ ρ := by
    have hpR : dist p p0 ≤ R := hR hp
    have heq : q - p0 = t • (p0 - p) := by
      rw [hq_def]
      module
    rw [dist_eq_norm, heq, norm_smul, Real.norm_of_nonneg ht.le, ← dist_eq_norm,
      dist_comm]
    have hnonneg : 0 ≤ dist p p0 := dist_nonneg
    calc t * dist p p0 ≤ t * (R + 1) := by
          exact mul_le_mul_of_nonneg_left (by linarith) ht.le
      _ = ρ := by rw [ht_def]; field_simp
  have hq : q ∈ closedBall p0 ρ := Metric.mem_closedBall.mpr hdist
  have hqQ : q ∈ Q := hclosed hq
  -- The point `p0` is the convex combination of `q` and `p` with weights `1 / (1 + t)`
  -- and `t / (1 + t)`.
  have h1t : (0 : ℝ) < 1 + t := by linarith
  have hq_eq : (1 + t) • p0 = q + t • p := by
    rw [hq_def, sub_add_cancel]
  have hconv : (1 / (1 + t)) • q + (t / (1 + t)) • p = p0 := by
    have hs : (t / (1 + t)) • p = (1 / (1 + t)) • (t • p) := by
      rw [smul_smul]
      congr 1
      ring
    rw [hs, ← smul_add, ← hq_eq, smul_smul, one_div, inv_mul_cancel₀ h1t.ne', one_smul]
  have hw1 : 0 ≤ 1 / (1 + t) := (div_pos one_pos h1t).le
  have hw2 : 0 ≤ t / (1 + t) := (div_pos ht h1t).le
  have hsum : 1 / (1 + t) + t / (1 + t) = 1 := by
    rw [← add_div, div_eq_one_iff_eq h1t.ne']
  have hineq := hf.2 hqQ hp hw1 hw2 hsum
  rw [hconv, smul_eq_mul, smul_eq_mul] at hineq
  have hfq : f q ≤ M := hmax hq
  have hmain : (1 + t) * f p0 ≤ f q + t * f p := by
    have h1 : (1 + t) * (1 / (1 + t) * f q + t / (1 + t) * f p) = f q + t * f p := by
      field_simp
    have h2 := mul_le_mul_of_nonneg_left hineq h1t.le
    rw [h1] at h2
    exact h2
  rw [div_le_iff₀ ht]
  linarith

end Riesz1

end
end
