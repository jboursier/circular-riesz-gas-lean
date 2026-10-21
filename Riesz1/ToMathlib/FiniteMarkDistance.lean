/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.MetricSpace.Basic

/-!
# Distance to a finite nonempty set of marks, capped at one

This is the radius used in Lemma 5.1. Its definition
uses a finite minimum, so it also describes the radius at marks and repeated marks.
-/

public section

namespace Riesz1

/-- The distance to a nonempty finite family of marks, capped at one. -/
noncomputable def cappedMarkDistance {X ι : Type*} [PseudoMetricSpace X]
    [Fintype ι] [Nonempty ι] (marks : ι → X) (x : X) : ℝ :=
  min 1 (Finset.univ.inf' Finset.univ_nonempty (fun j => dist x (marks j)))

theorem cappedMarkDistance_le_one {X ι : Type*} [PseudoMetricSpace X]
    [Fintype ι] [Nonempty ι] (marks : ι → X) (x : X) :
    cappedMarkDistance marks x ≤ 1 := min_le_left _ _

theorem cappedMarkDistance_le_dist {X ι : Type*} [PseudoMetricSpace X]
    [Fintype ι] [Nonempty ι] (marks : ι → X) (x : X) (j : ι) :
    cappedMarkDistance marks x ≤ dist x (marks j) :=
  (min_le_right _ _).trans (Finset.inf'_le _ (Finset.mem_univ j))

theorem cappedMarkDistance_pos {X ι : Type*} [MetricSpace X]
    [Fintype ι] [Nonempty ι] (marks : ι → X) (x : X)
    (hx : ∀ j, x ≠ marks j) : 0 < cappedMarkDistance marks x := by
  apply lt_min zero_lt_one
  exact (Finset.lt_inf'_iff Finset.univ_nonempty).mpr fun j _ => dist_pos.mpr (hx j)

/-- A finite sum of singular powers is controlled by the power of the nearest distance. -/
theorem sum_dist_rpow_le_cappedMarkDistance {X ι : Type*} [MetricSpace X]
    [Fintype ι] [Nonempty ι] (marks : ι → X) (x : X)
    (hx : ∀ j, x ≠ marks j) {e : ℝ} (he : e ≤ 0) :
    (∑ j, dist x (marks j) ^ e) ≤
      (Fintype.card ι : ℝ) * cappedMarkDistance marks x ^ e := by
  calc _ ≤ ∑ _j : ι, cappedMarkDistance marks x ^ e := by
         apply Finset.sum_le_sum
         intro j _
         exact Real.rpow_le_rpow_of_nonpos (cappedMarkDistance_pos marks x hx)
           (cappedMarkDistance_le_dist marks x j) he
       _ = _ := by simp

/-- Conversely the capped-distance power is bounded by one plus the sum of powers. -/
theorem cappedMarkDistance_rpow_le_one_add_sum {X ι : Type*} [PseudoMetricSpace X]
    [Fintype ι] [Nonempty ι] (marks : ι → X) (x : X) (e : ℝ) :
    cappedMarkDistance marks x ^ e ≤ 1 + ∑ j, dist x (marks j) ^ e := by
  classical
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_inf' (s := Finset.univ)
    Finset.univ_nonempty (fun j => dist x (marks j))
  unfold cappedMarkDistance
  rw [hj]
  rcases le_total 1 (dist x (marks j)) with h | h
  · rw [min_eq_left h, Real.one_rpow]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => by positivity)
  · rw [min_eq_right h]
    exact (Finset.single_le_sum (f := fun j => dist x (marks j) ^ e)
      (fun _ _ => by positivity) (Finset.mem_univ j)).trans
      (le_add_of_nonneg_left zero_le_one)

end Riesz1
