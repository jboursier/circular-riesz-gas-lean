/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Power sums over a tail of the integers

For a real exponent `a > 1` and an integer `J ≥ 1`, every finite set `S` of integers in `(J, N]`
satisfies `∑_{m ∈ S} m^{-a} ≤ J^{1-a}/(a-1)`. This is the discrete tail estimate used for the
exterior sums of Lemma 5.2.
-/

@[expose] public section

open Finset Set

namespace Riesz1

/-- **Tail of a power sum.** Let `a > 1` and `1 ≤ J`. Every finite set `S` of naturals with
`J < m ≤ N` for all `m ∈ S` satisfies `∑_{m ∈ S} m^{-a} ≤ J^{1-a}/(a-1)`. -/
theorem sum_natCast_rpow_neg_le_of_subset {a : ℝ} (ha : 1 < a) {J N : ℕ} (hJ : 1 ≤ J)
    (S : Finset ℕ) (hS : ∀ m ∈ S, J < m ∧ m ≤ N) :
    ∑ m ∈ S, (m : ℝ) ^ (-a) ≤ (J : ℝ) ^ (1 - a) / (a - 1) := by
  have hJr : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have he : 0 < a - 1 := by linarith
  have hJ0 : 0 ≤ (J : ℝ) ^ (1 - a) := Real.rpow_nonneg (by linarith) _
  by_cases hJN : J ≤ N
  swap
  · -- Then `S` is empty, since `J < m ≤ N < J` is impossible.
    have hS0 : S = ∅ := by
      ext m
      constructor
      · intro hm
        have := hS m hm
        omega
      · intro h
        exact absurd h (Finset.notMem_empty m)
    rw [hS0, Finset.sum_empty]
    exact div_nonneg hJ0 he.le
  -- Reindex `m ↦ m - 1` so that the sum runs over `Ico J N`, where the integral test applies.
  have hinj : Set.InjOn (fun m : ℕ => m - 1) S := by
    intro m hm m' hm' h
    have h1 := (hS m hm).1
    have h2 := (hS m' hm').1
    simp only at h
    omega
  have hsub : S.image (fun m : ℕ => m - 1) ⊆ Ico J N := by
    intro k hk
    rw [Finset.mem_image] at hk
    obtain ⟨m, hm, rfl⟩ := hk
    have h := hS m hm
    rw [Finset.mem_Ico]
    omega
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-a)) (Icc (J : ℝ) (N : ℝ)) := by
    intro x hx y hy hxy
    have hx0 : (0 : ℝ) < x := lt_of_lt_of_le (by linarith) hx.1
    exact Real.rpow_le_rpow_of_nonpos hx0 hxy (by linarith)
  have hint_le : ∑ k ∈ Ico J N, ((k + 1 : ℕ) : ℝ) ^ (-a) ≤
      ∫ x in (J : ℝ)..(N : ℝ), x ^ (-a) :=
    AntitoneOn.sum_le_integral_Ico hJN hanti
  have hJNr : (J : ℝ) ≤ N := by exact_mod_cast hJN
  have hzero : (0 : ℝ) ∉ uIcc (J : ℝ) (N : ℝ) := by
    intro h
    rw [Set.mem_uIcc] at h
    rcases h with h | h <;> linarith
  have hint : ∫ x in (J : ℝ)..(N : ℝ), x ^ (-a) =
      ((N : ℝ) ^ (-a + 1) - (J : ℝ) ^ (-a + 1)) / (-a + 1) :=
    integral_rpow (Or.inr ⟨by intro h; linarith, hzero⟩)
  have hNpos : 0 ≤ (N : ℝ) ^ (-(a - 1)) := Real.rpow_nonneg (by linarith) _
  have hbound : ∫ x in (J : ℝ)..(N : ℝ), x ^ (-a) ≤ (J : ℝ) ^ (1 - a) / (a - 1) := by
    rw [hint, show -a + 1 = -(a - 1) by ring, show 1 - a = -(a - 1) by ring, div_neg, ← neg_div,
      div_le_div_iff_of_pos_right he]
    linarith
  have hreindex : ∑ m ∈ S, (m : ℝ) ^ (-a) = ∑ k ∈ S.image (fun m : ℕ => m - 1),
      ((k + 1 : ℕ) : ℝ) ^ (-a) := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun m hm => ?_
    have h1 : m - 1 + 1 = m := Nat.sub_add_cancel (by have := (hS m hm).1; omega)
    rw [h1]
  have hsub_sum : ∑ k ∈ S.image (fun m : ℕ => m - 1), ((k + 1 : ℕ) : ℝ) ^ (-a) ≤
      ∑ k ∈ Ico J N, ((k + 1 : ℕ) : ℝ) ^ (-a) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => by positivity
  rw [hreindex]
  linarith

end Riesz1

end
