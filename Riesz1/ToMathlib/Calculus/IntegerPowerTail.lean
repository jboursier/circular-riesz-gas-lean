/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.Calculus.PowerSumFromPoint
public import Mathlib.Data.Int.Cast.Lemmas

/-!
# Two-sided power tails on integer sets

A finite subset of the integers outside a real radius has the same power-tail
estimate as the two one-sided integral tests, uniformly in the set.
-/

public section

noncomputable section

open Finset

namespace Riesz1

/-- The two-sided integer power tail, with a real cutoff. -/
theorem sum_int_abs_rpow_tail {a M : ℝ} (ha : 1 < a) (hM : 1 ≤ M)
    (S : Finset ℤ) (hS : ∀ j ∈ S, M ≤ |(j : ℝ)|) :
    ∑ j ∈ S, |(j : ℝ)| ^ (-a) ≤
      (2 * (1 + 1 / (a - 1))) * M ^ (1 - a) := by
  have hcast (j : ℤ) : (j.natAbs : ℝ) = |(j : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  let J := ⌈M⌉₊
  have hJ : 1 ≤ J := by
    have : (1 : ℝ) ≤ J := hM.trans (Nat.le_ceil M)
    exact_mod_cast this
  have hone (T : Finset ℤ) (hT : T ⊆ S)
      (hinj : Set.InjOn Int.natAbs T) :
      ∑ j ∈ T, |(j : ℝ)| ^ (-a) ≤ (1 + 1 / (a - 1)) * M ^ (1 - a) := by
    have hb := sum_natCast_rpow_neg_le_of_ge ha hJ (T.image Int.natAbs) (by
      intro k hk
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
      apply Nat.ceil_le.mpr
      simpa only [hcast] using hS j (hT hj))
    rw [Finset.sum_image hinj] at hb
    simp only [hcast] at hb
    apply hb.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.rpow_le_rpow_of_nonpos (by linarith) (Nat.le_ceil M) (by linarith)
  let Sneg := S.filter (fun j => j < 0)
  let Spos := S.filter (fun j => ¬j < 0)
  have hn : ∑ j ∈ Sneg, |(j : ℝ)| ^ (-a) ≤ (1 + 1 / (a - 1)) * M ^ (1 - a) := by
    apply hone Sneg (Finset.filter_subset _ _)
    intro i hi j hj he
    have hi0 := (Finset.mem_filter.mp hi).2
    have hj0 := (Finset.mem_filter.mp hj).2
    have he' := congrArg (fun k : ℕ => (k : ℤ)) he
    rw [Int.natCast_natAbs, Int.natCast_natAbs, abs_of_neg hi0, abs_of_neg hj0] at he'
    omega
  have hp : ∑ j ∈ Spos, |(j : ℝ)| ^ (-a) ≤ (1 + 1 / (a - 1)) * M ^ (1 - a) := by
    apply hone Spos (Finset.filter_subset _ _)
    intro i hi j hj he
    have hi0 := le_of_not_gt (Finset.mem_filter.mp hi).2
    have hj0 := le_of_not_gt (Finset.mem_filter.mp hj).2
    have he' := congrArg (fun k : ℕ => (k : ℤ)) he
    rw [Int.natCast_natAbs, Int.natCast_natAbs, abs_of_nonneg hi0, abs_of_nonneg hj0] at he'
    exact he'
  have he := Finset.sum_filter_add_sum_filter_not S (fun j => j < 0)
    (fun j => |(j : ℝ)| ^ (-a))
  change (∑ j ∈ Sneg, |(j : ℝ)| ^ (-a)) + (∑ j ∈ Spos, |(j : ℝ)| ^ (-a)) = _ at he
  rw [← he]
  linarith

end Riesz1

end
