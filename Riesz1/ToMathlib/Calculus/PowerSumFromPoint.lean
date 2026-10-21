/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.Calculus.DiscreteTailSum

/-!
# Power sums over a closed tail of the integers

The non-strict form of `sum_natCast_rpow_neg_le_of_subset`: the terms with `m ≥ J` are summed
through the terms with `m > J`, and the single term `m = J` is bounded by `J^{1-a}`. This is the
form needed for sums of `k^{-a}` over path lengths `k ≥ J` in the gap representative.
-/

@[expose] public section

open Finset

namespace Riesz1

/-- **Power sum from a point.** Let `a > 1` and `1 ≤ J`. Every finite set `S` of naturals with
`J ≤ m` for all `m ∈ S` satisfies `∑_{m ∈ S} m^{-a} ≤ (1 + 1/(a-1)) J^{1-a}`. -/
theorem sum_natCast_rpow_neg_le_of_ge {a : ℝ} (ha : 1 < a) {J : ℕ} (hJ : 1 ≤ J)
    (S : Finset ℕ) (hS : ∀ m ∈ S, J ≤ m) :
    ∑ m ∈ S, (m : ℝ) ^ (-a) ≤ (1 + 1 / (a - 1)) * (J : ℝ) ^ (1 - a) := by
  have hJr : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have he : 0 < a - 1 := by linarith
  -- split `S` into the term `m = J` and the terms `m > J`
  have hfilt : S.filter (fun m => ¬ m = J) = S.filter (fun m => J < m) :=
    Finset.filter_congr fun m hm => ⟨fun h => lt_of_le_of_ne (hS m hm) (Ne.symm h),
      fun h => by omega⟩
  have hsplit : ∑ m ∈ S, (m : ℝ) ^ (-a) =
      ∑ m ∈ S.filter (fun m => m = J), (m : ℝ) ^ (-a) +
        ∑ m ∈ S.filter (fun m => J < m), (m : ℝ) ^ (-a) := by
    rw [← Finset.sum_filter_add_sum_filter_not S (fun m => m = J), hfilt]
  have h1 : ∑ m ∈ S.filter (fun m => m = J), (m : ℝ) ^ (-a) ≤ (J : ℝ) ^ (1 - a) := by
    have hsub : S.filter (fun m => m = J) ⊆ {J} := by
      intro m hm
      rw [Finset.mem_filter] at hm
      rw [Finset.mem_singleton]
      exact hm.2
    calc ∑ m ∈ S.filter (fun m => m = J), (m : ℝ) ^ (-a)
        ≤ ∑ m ∈ ({J} : Finset ℕ), (m : ℝ) ^ (-a) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun m _ _ => Real.rpow_nonneg (Nat.cast_nonneg m) _)
      _ = (J : ℝ) ^ (-a) := by simp
      _ ≤ (J : ℝ) ^ (1 - a) :=
          Real.rpow_le_rpow_of_exponent_le hJr (by linarith)
  have h2 : ∑ m ∈ S.filter (fun m => J < m), (m : ℝ) ^ (-a) ≤ (J : ℝ) ^ (1 - a) / (a - 1) := by
    refine sum_natCast_rpow_neg_le_of_subset ha hJ _ (N := S.sup id) ?_
    intro m hm
    rw [Finset.mem_filter] at hm
    exact ⟨hm.2, Finset.le_sup (f := id) hm.1⟩
  rw [hsplit]
  calc _ ≤ (J : ℝ) ^ (1 - a) + (J : ℝ) ^ (1 - a) / (a - 1) := add_le_add h1 h2
    _ = (1 + 1 / (a - 1)) * (J : ℝ) ^ (1 - a) := by ring

end Riesz1
