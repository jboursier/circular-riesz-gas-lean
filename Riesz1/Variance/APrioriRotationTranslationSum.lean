/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.Calculus.DiscreteTailSum
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Power sums over label distances for the translation error

Translation error in the proof of Lemma 5.2. The good-event estimate of the translation
error sums a derivative majorant over the window labels, and a window label at distance `d` from
the origin contributes a power of `d`. These are the two real sums needed:

* `sum_Icc_inv_le`: the harmonic sum `∑_{1 ≤ d ≤ M} 1/d` is at most `1 + log M`.
* `sum_Icc_min_rpow_le`: the truncated power sum `∑_{1 ≤ d ≤ M} min(2A/d, 1/2)^p` is at most
  `(2 + 2^p/(p - 1)) A` for `A ≥ 1` and `p > 1`, uniformly in `M`.
-/

@[expose] public section

open Finset

namespace Riesz1

/-- **Harmonic sum.** For every natural `M`, `∑_{1 ≤ d ≤ M} 1/d ≤ 1 + log M`. -/
theorem sum_Icc_inv_le (M : ℕ) : ∑ d ∈ Icc 1 M, (1 : ℝ) / d ≤ 1 + Real.log M := by
  induction M with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp
    · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      -- `log (n + 1) - log n ≥ 1 / (n + 1)`, from `log y ≤ y - 1` at `y = n / (n + 1)`.
      have hy : Real.log ((n : ℝ) / ((n : ℝ) + 1)) ≤ (n : ℝ) / ((n : ℝ) + 1) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      have hlog : Real.log ((n : ℝ) / ((n : ℝ) + 1)) = Real.log n - Real.log ((n : ℝ) + 1) := by
        rw [Real.log_div hn'.ne' (by positivity)]
      have hfrac : (n : ℝ) / ((n : ℝ) + 1) - 1 = -(1 / ((n : ℝ) + 1)) := by
        field_simp
        ring
      have hstep : 1 / ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1) - Real.log n := by
        linarith
      push_cast
      linarith

/-- **Truncated power sum over distances.** Let `A ≥ 1` and `p > 1`. Then for every natural `M`,
`∑_{1 ≤ d ≤ M} min(2A/d, 1/2)^p ≤ (2 + 2^p/(p-1)) A`. -/
theorem sum_Icc_min_rpow_le {A p : ℝ} (hA : 1 ≤ A) (hp : 1 < p) (M : ℕ) :
    ∑ d ∈ Icc 1 M, min (2 * A / (d : ℝ)) (1 / 2) ^ p ≤ (2 + 2 ^ p / (p - 1)) * A := by
  set n : ℕ := ⌊2 * A⌋₊ with hn_def
  have hn2 : 2 ≤ n := Nat.le_floor (by norm_num; linarith)
  have hnA : A ≤ (n : ℝ) := by
    have h1 := Nat.lt_floor_add_one (2 * A)
    rw [← hn_def] at h1
    linarith
  have hn2A : (n : ℝ) ≤ 2 * A := Nat.floor_le (by linarith)
  -- Pointwise: each term is at most an indicator of `d ≤ n` plus a tail power.
  have hpoint : ∀ d ∈ Icc 1 M,
      min (2 * A / (d : ℝ)) (1 / 2) ^ p ≤
        (if d ≤ n then (1 : ℝ) else 0) + (if n < d then (2 * A) ^ p * (d : ℝ) ^ (-p) else 0) := by
    intro d hd
    have hd1 : 1 ≤ d := (mem_Icc.1 hd).1
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
    by_cases hdn : d ≤ n
    · have hnd : ¬ n < d := by omega
      simp only [hdn, hnd, ↓reduceIte, add_zero]
      have h0 : 0 ≤ min (2 * A / (d : ℝ)) (1 / 2) := le_min (by positivity) (by norm_num)
      have h1 : min (2 * A / (d : ℝ)) (1 / 2) ≤ 1 := le_trans (min_le_right _ _) (by norm_num)
      exact Real.rpow_le_one h0 h1 (by linarith)
    · have hnd : n < d := by omega
      simp only [hdn, hnd, ↓reduceIte, zero_add]
      have hdA : 2 * A < (d : ℝ) := by
        have : (n : ℝ) + 1 ≤ (d : ℝ) := by exact_mod_cast (by omega : n + 1 ≤ d)
        have h2 := Nat.lt_floor_add_one (2 * A)
        rw [← hn_def] at h2
        linarith
      have hle : min (2 * A / (d : ℝ)) (1 / 2) ≤ 2 * A / (d : ℝ) := min_le_left _ _
      have h0 : 0 ≤ min (2 * A / (d : ℝ)) (1 / 2) := le_min (by positivity) (by norm_num)
      calc min (2 * A / (d : ℝ)) (1 / 2) ^ p ≤ (2 * A / (d : ℝ)) ^ p :=
            Real.rpow_le_rpow h0 hle (by linarith)
        _ = (2 * A) ^ p * (d : ℝ) ^ (-p) := by
            rw [Real.div_rpow (by linarith) hdpos.le, Real.rpow_neg hdpos.le, div_eq_mul_inv,
              ← Real.rpow_neg hdpos.le]
  calc ∑ d ∈ Icc 1 M, min (2 * A / (d : ℝ)) (1 / 2) ^ p
      ≤ ∑ d ∈ Icc 1 M, ((if d ≤ n then (1 : ℝ) else 0) +
          (if n < d then (2 * A) ^ p * (d : ℝ) ^ (-p) else 0)) :=
        Finset.sum_le_sum hpoint
    _ = ∑ d ∈ Icc 1 M, (if d ≤ n then (1 : ℝ) else 0) +
          ∑ d ∈ Icc 1 M, (if n < d then (2 * A) ^ p * (d : ℝ) ^ (-p) else 0) :=
        Finset.sum_add_distrib
    _ ≤ (2 + 2 ^ p / (p - 1)) * A := by
        -- The first sum counts the labels `d ≤ n`, at most `n ≤ 2A` of them.
        have hfirst : ∑ d ∈ Icc 1 M, (if d ≤ n then (1 : ℝ) else 0) ≤ 2 * A := by
          rw [Finset.sum_boole]
          have hsub : (Icc 1 M).filter (fun d => d ≤ n) ⊆ Icc 1 n := by
            intro d hd
            rw [mem_filter, mem_Icc] at hd
            rw [mem_Icc]
            exact ⟨hd.1.1, hd.2⟩
          have hcard : (((Icc 1 M).filter (fun d => d ≤ n)).card : ℝ) ≤ n := by
            have := Finset.card_le_card hsub
            rw [Nat.card_Icc] at this
            have h' : ((Icc 1 M).filter (fun d => d ≤ n)).card ≤ n := by omega
            exact_mod_cast h'
          linarith
        -- The second sum is a tail of `d^{-p}` above `n`.
        have hsecond : ∑ d ∈ Icc 1 M, (if n < d then (2 * A) ^ p * (d : ℝ) ^ (-p) else 0) ≤
            (2 * A) ^ p * (n : ℝ) ^ (1 - p) / (p - 1) := by
          rw [← Finset.sum_filter, ← Finset.mul_sum]
          have hS : ∀ m ∈ (Icc 1 M).filter (fun d => n < d), n < m ∧ m ≤ M := by
            intro m hm
            rw [mem_filter, mem_Icc] at hm
            exact ⟨hm.2, hm.1.2⟩
          have := sum_natCast_rpow_neg_le_of_subset (a := p) hp (J := n) (N := M) (by omega)
            ((Icc 1 M).filter (fun d => n < d)) hS
          rw [mul_div_assoc]
          exact mul_le_mul_of_nonneg_left this (by positivity)
        -- Compare `n^{1-p}` with `A^{1-p}`.
        have hnp : (n : ℝ) ^ (1 - p) ≤ A ^ (1 - p) :=
          Real.rpow_le_rpow_of_nonpos (by linarith) hnA (by linarith)
        have hfin : (2 * A) ^ p * A ^ (1 - p) = 2 ^ p * A := by
          rw [Real.mul_rpow (by linarith) (by linarith)]
          have : A ^ p * A ^ (1 - p) = A := by
            rw [← Real.rpow_add (by linarith)]
            norm_num
          calc 2 ^ p * A ^ p * A ^ (1 - p) = 2 ^ p * (A ^ p * A ^ (1 - p)) := by ring
            _ = 2 ^ p * A := by rw [this]
        have hbound : (2 * A) ^ p * (n : ℝ) ^ (1 - p) / (p - 1) ≤ 2 ^ p / (p - 1) * A := by
          have hp1 : 0 < p - 1 := by linarith
          have hmul : (2 * A) ^ p * (n : ℝ) ^ (1 - p) ≤ 2 ^ p * A := by
            calc (2 * A) ^ p * (n : ℝ) ^ (1 - p) ≤ (2 * A) ^ p * A ^ (1 - p) :=
                  mul_le_mul_of_nonneg_left hnp (by positivity)
              _ = 2 ^ p * A := hfin
          calc (2 * A) ^ p * (n : ℝ) ^ (1 - p) / (p - 1) ≤ 2 ^ p * A / (p - 1) :=
                (div_le_div_iff_of_pos_right hp1).2 hmul
            _ = 2 ^ p / (p - 1) * A := by ring
        nlinarith [hfirst, hsecond, hbound]

end Riesz1
