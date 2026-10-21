/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Tactic

/-!
# Localizing finitely many power singularities on a circle

Around any real lift, a finite sum of negative powers of circular distances is bounded
by a single power of the distance to that lift on a sufficiently small punctured interval.
The radius also excludes all marked points. This is the localization used in the admissibility
regularity lemma.
-/

public section

open Set Filter
open scoped Topology

namespace Riesz1.CircleSingularity

/-- The quotient distance is the real distance for differences of length at most half a period. -/
theorem dist_coe_eq_abs_sub {T : ℝ} (hT : 0 < T) {x y : ℝ} (hxy : |x - y| ≤ T / 2) :
    dist (x : AddCircle T) (y : AddCircle T) = |x - y| := by
  rw [dist_eq_norm, ← QuotientAddGroup.mk_sub]
  exact (AddCircle.norm_coe_eq_abs_iff T hT.ne').mpr (by simpa [abs_of_pos hT] using hxy)

/-- All lifts of finitely many circle marks form a countable exceptional set. -/
theorem countable_marked_lifts {T : ℝ} {ι : Type*} [Countable ι] (marks : ι → ℝ) :
    {x : ℝ | ∃ j, (x : AddCircle T) = (marks j : AddCircle T)}.Countable := by
  apply (countable_range (fun jk : ι × ℤ => marks jk.1 + jk.2 * T)).mono
  rintro x ⟨j, hj⟩
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp
    (QuotientAddGroup.eq_iff_sub_mem.mp hj)
  refine ⟨(j, k), ?_⟩
  rw [zsmul_eq_mul] at hk
  dsimp only
  linarith

/-- Finite circular singularities reduce locally to one punctured power bound.
The constant and radius here are local. No uniformity in the circle length is asserted. -/
theorem exists_punctured_power_bound {T : ℝ} (hT : 0 < T) {ι : Type*} [Fintype ι]
    (marks : ι → AddCircle T) {e : ℝ} (he : e < 0) (a : ℝ) :
    ∃ R C : ℝ, 0 < R ∧ R ≤ 1 ∧ 0 ≤ C ∧
      ∀ t : ℝ, 0 < |t - a| → |t - a| ≤ R →
        (∀ j, (t : AddCircle T) ≠ marks j) ∧
        (∑ j, dist (t : AddCircle T) (marks j) ^ e) ≤ C * |t - a| ^ e := by
  classical
  have : Fact (0 < T) := ⟨hT⟩
  let D : ι → ℝ := fun j => if (a : AddCircle T) = marks j then 1
    else dist (a : AddCircle T) (marks j) ^ e + 1
  have hD : ∀ j, 0 ≤ D j := by
    intro j
    dsimp [D]
    split_ifs <;> positivity
  have hlocal : ∀ j, ∀ᶠ t : ℝ in 𝓝 a,
      (a : AddCircle T) ≠ marks j →
        (t : AddCircle T) ≠ marks j ∧ dist (t : AddCircle T) (marks j) ^ e ≤ D j := by
    intro j
    by_cases hj : (a : AddCircle T) = marks j
    · exact Filter.Eventually.of_forall fun _ h => (h hj).elim
    · have hd : ContinuousAt (fun t : ℝ => dist (t : AddCircle T) (marks j)) a :=
        (AddCircle.continuous_mk' T).continuousAt.dist continuousAt_const
      have hp := hd.rpow_const (p := e) (Or.inl (dist_ne_zero.mpr hj))
      have hpos := hd.eventually (lt_mem_nhds (dist_pos.mpr hj))
      have hupper := hp.eventually (gt_mem_nhds (lt_add_one _))
      filter_upwards [hpos, hupper] with t ht htu _
      exact ⟨dist_pos.mp ht, by simpa [D, hj] using htu.le⟩
  have hall := Filter.eventually_all.mpr hlocal
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hall
  let R := min (r / 2) (min 1 (T / 2))
  have hR : 0 < R := lt_min (by linarith) (lt_min zero_lt_one (by linarith))
  have hRr : R < r := (min_le_left _ _).trans_lt (by linarith)
  have hR1 : R ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hRT : R ≤ T / 2 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨R, ∑ j, D j, hR, hR1, Finset.sum_nonneg (fun j _ => hD j), ?_⟩
  intro t ht htR
  have htp : 1 ≤ |t - a| ^ e :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht (htR.trans hR1) he.le
  have hdist := dist_coe_eq_abs_sub hT (htR.trans hRT)
  have hballt := hball (show dist t a < r by rw [Real.dist_eq]; exact htR.trans_lt hRr)
  have heach : ∀ j, (t : AddCircle T) ≠ marks j ∧
      dist (t : AddCircle T) (marks j) ^ e ≤ D j * |t - a| ^ e := by
    intro j
    by_cases hj : (a : AddCircle T) = marks j
    · rw [← hj, hdist]
      exact ⟨fun h => (ne_of_gt ht) (by simpa [h] using hdist.symm),
        by simp [D, hj]⟩
    · obtain ⟨hne, hle⟩ := hballt j hj
      exact ⟨hne, hle.trans (le_mul_of_one_le_right (hD j) htp)⟩
  refine ⟨fun j => (heach j).1, ?_⟩
  simpa only [Finset.sum_mul] using Finset.sum_le_sum (fun j _ => (heach j).2)

end Riesz1.CircleSingularity
