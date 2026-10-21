/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.PeriodicMarkCutoff
public import Mathlib.Analysis.Normed.Group.AddCircle
public import Mathlib.Tactic

/-!
# Quantitative periodic cutoffs at varying radii

The existing `markCut` and `cutoffBump` give the actual cutoffs.
This file supplies their uniform scaling bound and the partition
properties of sums around separated marks. It introduces no new cutoff.
-/

public section

open Set Filter Topology
open scoped ContDiff

namespace Riesz1

theorem abs_cutRep_eq_dist (L x a : ℝ) :
    |cutRep L (x - a)| = dist (x : AddCircle L) (a : AddCircle L) := by
  rw [dist_eq_norm, ← AddCircle.coe_sub, AddCircle.norm_eq]
  simp only [cutRep, div_eq_mul_inv, mul_comm]

theorem cutoffBump_eq_rescale {r : ℝ} (hr : r ≠ 0) (t : ℝ) :
    cutoffBump r t = cutoffBump 1 (t / r) := by
  unfold cutoffBump
  congr 2
  field_simp

/-- One derivative bound chosen before every radius, period and center. -/
theorem exists_scaled_markCut_deriv_bound :
    ∃ D : ℝ, 0 < D ∧ ∀ (L r a : ℝ), 0 < L → 0 < r → 4*r < L →
      ∀ x : ℝ, |deriv (markCut (cutoffBump r) L a) x| ≤ D / r := by
  obtain ⟨M, _, hM, _⟩ := exists_bounds_deriv_bump (contDiff_cutoffBump 1)
    (fun t ht => cutoffBump_eq_zero (by norm_num) ht)
  let D := max M 0 + 1
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D, hD, fun L r a hL hr hroom x => ?_⟩
  apply abs_deriv_markCut_le (fun t ht => cutoffBump_eq_zero hr ht) hL hroom
  intro t
  have he : cutoffBump r = fun u => cutoffBump 1 (u/r) :=
    funext (cutoffBump_eq_rescale hr.ne')
  have hd : deriv (cutoffBump r) t = deriv (cutoffBump 1) (t/r) / r := by
    rw [he]
    exact (by simpa only [mul_one_div, Function.comp_def, id_eq] using
      (((contDiff_cutoffBump 1).differentiable (by simp) (t/r)).hasDerivAt.comp t
        ((hasDerivAt_id t).div_const r)).deriv)
  rw [hd, abs_div, abs_of_pos hr]
  exact div_le_div_of_nonneg_right ((hM _).trans (by dsimp [D]; linarith [le_max_left M 0])) hr.le

theorem markCut_cutoffBump_mem_Icc (L r a x : ℝ) :
    markCut (cutoffBump r) L a x ∈ Icc (0 : ℝ) 1 :=
  cutoffBump_mem_Icc _ _

theorem markCut_cutoffBump_eq_one {L r a x : ℝ}
    (hx : dist (x : AddCircle L) (a : AddCircle L) ≤ r) :
    markCut (cutoffBump r) L a x = 1 := by
  apply cutoffBump_eq_one
  rwa [abs_cutRep_eq_dist]

theorem markCut_cutoffBump_eq_zero {L r a x : ℝ} (hr : 0 < r)
    (hx : 2*r ≤ dist (x : AddCircle L) (a : AddCircle L)) :
    markCut (cutoffBump r) L a x = 0 := by
  apply cutoffBump_eq_zero hr
  rwa [abs_cutRep_eq_dist]

theorem contDiff_markCut_cutoffBump {L r : ℝ} (hL : 0 < L) (hr : 0 < r)
    (hroom : 4*r < L) (a : ℝ) :
    ContDiff ℝ ∞ (markCut (cutoffBump r) L a) :=
  contDiff_markCut (contDiff_cutoffBump r)
    (fun _t ht => cutoffBump_eq_zero hr ht) hL hroom a

section FiniteMarks

variable {ι : Type*} [Fintype ι]

/-- At most one summand is nonzero when the cutoff neighborhoods are disjoint. -/
theorem sum_markCut_cutoffBump_mem_Icc {L r : ℝ} (hr : 0 < r) (a : ι → ℝ)
    (hsep : ∀ i j, i ≠ j → 4*r ≤ dist (a i : AddCircle L) (a j : AddCircle L))
    (x : ℝ) :
    (∑ j, markCut (cutoffBump r) L (a j) x) ∈ Icc (0 : ℝ) 1 := by
  classical
  refine ⟨Finset.sum_nonneg (fun j _ => (markCut_cutoffBump_mem_Icc L r (a j) x).1), ?_⟩
  by_cases hex : ∃ j, markCut (cutoffBump r) L (a j) x ≠ 0
  · obtain ⟨j, hj⟩ := hex
    have hjd : dist (x : AddCircle L) (a j : AddCircle L) < 2*r := by
      by_contra hn
      exact hj (markCut_cutoffBump_eq_zero hr (le_of_not_gt hn))
    have hz : ∀ k, k ≠ j → markCut (cutoffBump r) L (a k) x = 0 := by
      intro k hkj
      apply markCut_cutoffBump_eq_zero hr
      have htri := dist_triangle (a k : AddCircle L) (x : AddCircle L) (a j : AddCircle L)
      linarith [hsep k j hkj, dist_comm (a k : AddCircle L) (x : AddCircle L)]
    rw [Finset.sum_eq_single j (fun k _ hkj => hz k hkj) (by simp)]
    exact (markCut_cutoffBump_mem_Icc L r (a j) x).2
  · push Not at hex
    simp only [hex, Finset.sum_const_zero, zero_le_one]

/-- The sum is exactly one in each inner neighborhood. -/
theorem sum_markCut_cutoffBump_eq_one {L r : ℝ} (hr : 0 < r) (a : ι → ℝ)
    (hsep : ∀ i j, i ≠ j → 4*r ≤ dist (a i : AddCircle L) (a j : AddCircle L))
    {x : ℝ} (j : ι) (hx : dist (x : AddCircle L) (a j : AddCircle L) ≤ r) :
    (∑ k, markCut (cutoffBump r) L (a k) x) = 1 := by
  classical
  rw [Finset.sum_eq_single j ?_ (by simp), markCut_cutoffBump_eq_one hx]
  intro k _ hkj
  apply markCut_cutoffBump_eq_zero hr
  have htri := dist_triangle (a k : AddCircle L) (x : AddCircle L) (a j : AddCircle L)
  linarith [hsep k j hkj, dist_comm (a k : AddCircle L) (x : AddCircle L)]

theorem sum_markCut_cutoffBump_eq_zero {L r : ℝ} (hr : 0 < r) (a : ι → ℝ)
    {x : ℝ} (hx : ∀ j, 2*r ≤ dist (x : AddCircle L) (a j : AddCircle L)) :
    (∑ j, markCut (cutoffBump r) L (a j) x) = 0 :=
  Finset.sum_eq_zero (fun j _ => markCut_cutoffBump_eq_zero hr (hx j))

/-- Smooth finite sums with the derivative bound proportional to the number of marks. -/
theorem sum_markCut_cutoffBump_smooth_bounds :
    ∃ D : ℝ, 0 < D ∧ ∀ (L r : ℝ), 0 < L → 0 < r → 4*r < L →
      ∀ a : ι → ℝ,
        ContDiff ℝ ∞ (fun x => ∑ j, markCut (cutoffBump r) L (a j) x) ∧
        ∀ x, |deriv (fun t => ∑ j, markCut (cutoffBump r) L (a j) t) x| ≤
          (Fintype.card ι : ℝ) * D / r := by
  obtain ⟨D, hD, hb⟩ := exists_scaled_markCut_deriv_bound
  refine ⟨D, hD, fun L r hL hr hroom a => ⟨?_, fun x => ?_⟩⟩
  · exact ContDiff.sum (fun j _ => contDiff_markCut_cutoffBump hL hr hroom (a j))
  · have he : (fun t => ∑ j, markCut (cutoffBump r) L (a j) t) =
        ∑ j, markCut (cutoffBump r) L (a j) := by
      ext t
      simp
    rw [he]
    rw [deriv_sum (fun j _ =>
      (contDiff_markCut_cutoffBump hL hr hroom (a j)).differentiable (by simp) x)]
    calc
      _ ≤ ∑ j, |deriv (markCut (cutoffBump r) L (a j)) x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : ι, D/r := Finset.sum_le_sum (fun j _ => hb L r (a j) hL hr hroom x)
      _ = _ := by simp [div_eq_mul_inv, mul_assoc]

end FiniteMarks

end Riesz1
