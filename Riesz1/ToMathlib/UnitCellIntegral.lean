/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Integrals over unit cells centred at integers

The unit cells `[k - 1/2, k + 1/2]` centred at the integers `a ≤ k < b` tile the interval
`[a - 1/2, b - 1/2]`. For a function integrable on that interval, the integrals over the cells add
up to the integral over the interval. This tiling identity compares a sum over lattice points with
an integral, as in the quadrature of the gradient splitting
(Lemma 5.7).
-/

@[expose] public section

open MeasureTheory intervalIntegral

namespace Riesz1

/-- The unit cells centred at the integers `a ≤ k < b` tile `[a - 1/2, b - 1/2]`. -/
theorem sum_Ico_unitCell_integral {f : ℝ → ℝ} {a b : ℤ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume ((a : ℝ) - 1 / 2) ((b : ℝ) - 1 / 2)) :
    ∑ k ∈ Finset.Ico a b, ∫ v in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), f v
      = ∫ v in ((a : ℝ) - 1 / 2)..((b : ℝ) - 1 / 2), f v := by
  induction b, hab using Int.leInduction with
  | base => simp
  | succ b hb ih =>
    have hab' : (a : ℝ) - 1 / 2 ≤ (b : ℝ) - 1 / 2 := by
      have : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
      linarith
    have hfb : IntervalIntegrable f volume ((a : ℝ) - 1 / 2) ((b : ℝ) - 1 / 2) := by
      refine hf.mono_set ?_
      rw [Set.uIcc_of_le hab', Set.uIcc_of_le (by push_cast; linarith)]
      apply Set.Icc_subset_Icc le_rfl
      push_cast
      linarith
    have hcell : IntervalIntegrable f volume ((b : ℝ) - 1 / 2) ((b : ℝ) + 1 / 2) := by
      refine hf.mono_set ?_
      rw [Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by push_cast; linarith)]
      apply Set.Icc_subset_Icc
      · linarith
      · push_cast
        linarith
    have hset : Finset.Ico a (b + 1) = insert b (Finset.Ico a b) := by
      ext k
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    have hbeq : ((b + 1 : ℤ) : ℝ) - 1 / 2 = (b : ℝ) + 1 / 2 := by
      push_cast
      ring
    rw [hset, Finset.sum_insert (by simp), ih hfb, hbeq,
      ← intervalIntegral.integral_add_adjacent_intervals hfb hcell]
    ring

end Riesz1
