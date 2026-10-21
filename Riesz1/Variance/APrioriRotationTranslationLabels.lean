/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriGoodComparison
public import Riesz1.Variance.Window

/-!
# Label counts for the translation error

Part of Lemma 5.2 (the rotation part), translation error. These are the counting facts about the
window `I_γ` that the translation estimate uses:

* the origin label and the next label lie in the window.
* a window label has label distance at most `4 K^γ` from the origin label, and the window has at
  most `9 K^γ` labels.
* a sum over window labels of a function of the label distance is at most twice the sum over the
  distance values, since each distance is taken by at most two labels.
* at most `2 m + 1` labels lie within label distance `m` of the origin label.
-/

@[expose] public section

open Finset

namespace Riesz1

/-- The label distance `d(i, 1)` is symmetric in its two labels. -/
theorem cyclicIndexDistance_comm' (N : ℕ+) (i j : Fin (N : ℕ)) :
    cyclicIndexDistance N i j = cyclicIndexDistance N j i := by
  unfold cyclicIndexDistance
  rw [Nat.dist_comm]

/-- The time `t_γ` of the window is nonnegative when `K ≥ 1`. -/
theorem windowTime_nonneg' {N : ℕ+} {K γ : ℝ} (hK : 1 ≤ K) : 0 ≤ windowTime N K γ := by
  have hKγ : 0 ≤ K ^ γ := Real.rpow_nonneg (by linarith) γ
  unfold windowTime
  split_ifs with h
  · exact div_nonneg hKγ (Nat.cast_nonneg _)
  · norm_num

/-- The origin label `0` (the paper's label `1`) lies in the window. -/
theorem origin_mem_window (N : ℕ+) {K γ : ℝ} (hK : 1 ≤ K) :
    (⟨0, N.pos⟩ : Fin (N : ℕ)) ∈ window N K γ := by
  unfold window windowLabels
  rw [mem_filter]
  refine ⟨mem_univ _, ?_⟩
  have h0 : labelDistToOne N ⟨0, N.pos⟩ = 0 := by
    unfold labelDistToOne cyclicIndexDistance
    simp
  rw [h0]
  have hw := windowTime_nonneg' (N := N) (γ := γ) hK
  push_cast
  exact mul_nonneg (Nat.cast_nonneg _) hw

/-- The next label `1` lies in the window when `N ≥ 2`. -/
theorem one_mem_window (N : ℕ+) (hN : 2 ≤ (N : ℕ)) {K γ : ℝ} (hK : 1 ≤ K) (hγ : 0 ≤ γ) :
    (⟨1, by omega⟩ : Fin (N : ℕ)) ∈ window N K γ := by
  have hd : labelDistToOne N ⟨1, by omega⟩ = 1 := by
    rw [labelDistToOne_eq]
    simp only
    omega
  by_cases h : K ^ γ < ((N : ℕ) : ℝ) / 8
  · unfold window windowLabels
    rw [mem_filter, windowTime_of_lt h, hd]
    refine ⟨mem_univ _, ?_⟩
    have hN0 : (0 : ℝ) < ((N : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < (N : ℕ) by omega)
    rw [mul_div_cancel₀ _ hN0.ne']
    have : (1 : ℝ) ≤ K ^ γ := Real.one_le_rpow hK hγ
    exact_mod_cast this
  · rw [window_full h]
    exact mem_univ _

/-- A window label has label distance at most `4 K^γ` from the origin label. -/
theorem labelDist_le_of_mem_window {N : ℕ+} {K γ : ℝ} (hK : 1 ≤ K) {i : Fin (N : ℕ)}
    (hi : i ∈ window N K γ) : (labelDistToOne N i : ℝ) ≤ 4 * K ^ γ := by
  have hKγ : 0 ≤ K ^ γ := Real.rpow_nonneg (by linarith) γ
  by_cases h : K ^ γ < ((N : ℕ) : ℝ) / 8
  · unfold window windowLabels at hi
    rw [mem_filter, windowTime_of_lt h] at hi
    have hN0 : (0 : ℝ) < ((N : ℕ) : ℝ) := by
      have : 0 < ((N : ℕ) : ℝ) / 8 := lt_of_le_of_lt hKγ h
      linarith
    have h2 := hi.2
    rw [mul_div_cancel₀ _ hN0.ne'] at h2
    linarith
  · rw [window_full h] at hi
    have hle := labelDistToOne_le_half N i
    have h8 : ((N : ℕ) : ℝ) / 8 ≤ K ^ γ := le_of_not_gt h
    linarith

/-- The window has at most `9 K^γ` labels. -/
theorem card_window_le_of_one_le {N : ℕ+} {K γ : ℝ} (hK : 1 ≤ K) (hγ : 0 ≤ γ) :
    ((window N K γ).card : ℝ) ≤ 9 * K ^ γ := by
  have hKγ1 : (1 : ℝ) ≤ K ^ γ := Real.one_le_rpow hK hγ
  by_cases h : K ^ γ < ((N : ℕ) : ℝ) / 8
  · have hN0 : (0 : ℝ) < ((N : ℕ) : ℝ) := by
      have hKγ0 : 0 ≤ K ^ γ := Real.rpow_nonneg (by linarith) γ
      have : 0 < ((N : ℕ) : ℝ) / 8 := lt_of_le_of_lt hKγ0 h
      linarith
    have hc : (window N K γ).card ≤ 2 * ⌊((N : ℕ) : ℝ) * windowTime N K γ⌋₊ + 1 :=
      card_windowLabels_le N (windowTime N K γ)
    have hNt : ((N : ℕ) : ℝ) * windowTime N K γ = K ^ γ := by
      rw [windowTime_of_lt h, mul_div_cancel₀ _ hN0.ne']
    rw [hNt] at hc
    have hfl : ((⌊K ^ γ⌋₊ : ℕ) : ℝ) ≤ K ^ γ := Nat.floor_le (Real.rpow_nonneg (by linarith) γ)
    have hc' : ((window N K γ).card : ℝ) ≤ 2 * ((⌊K ^ γ⌋₊ : ℕ) : ℝ) + 1 := by
      exact_mod_cast hc
    linarith
  · rw [window_full h, Finset.card_univ, Fintype.card_fin]
    have h8 : ((N : ℕ) : ℝ) / 8 ≤ K ^ γ := le_of_not_gt h
    have : ((N : ℕ) : ℝ) ≤ 8 * K ^ γ := by linarith
    linarith

/-- Fibre bound: a sum over window labels of `F` at the label distance is at most twice the sum
of `F` over the set `T` of distance values, since each distance value is taken by at most two
labels. -/
theorem sum_labelDist_le_two_mul {N : ℕ+} (S : Finset (Fin (N : ℕ))) {F : ℕ → ℝ}
    (hF : ∀ d, 0 ≤ F d) {T : Finset ℕ} (hT : ∀ i ∈ S, labelDistToOne N i ∈ T) :
    ∑ i ∈ S, F (labelDistToOne N i) ≤ 2 * ∑ d ∈ T, F d := by
  rw [← Finset.sum_fiberwise_of_maps_to hT, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d _
  have hconst : ∑ i ∈ S.filter (fun i => labelDistToOne N i = d), F (labelDistToOne N i)
      = ((S.filter fun i => labelDistToOne N i = d).card : ℝ) * F d := by
    rw [Finset.sum_congr rfl (fun i hi => by rw [(mem_filter.1 hi).2]), Finset.sum_const,
      nsmul_eq_mul]
  have hc : (S.filter fun i => labelDistToOne N i = d).card ≤ 2 := by
    have hsub : (S.filter fun i => labelDistToOne N i = d).card ≤
        ({d, (N : ℕ) - d} : Finset ℕ).card := by
      apply Finset.card_le_card_of_injOn (fun i : Fin (N : ℕ) => (i : ℕ))
      · intro i hi
        have hi' := (mem_filter.1 hi).2
        rw [labelDistToOne_eq] at hi'
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff]
        omega
      · intro i _ j _ hij
        exact Fin.ext hij
    exact hsub.trans Finset.card_le_two
  rw [hconst]
  have hd := hF d
  have hc' : ((S.filter fun i => labelDistToOne N i = d).card : ℝ) ≤ 2 := by
    exact_mod_cast hc
  nlinarith

/-- At most `2 m + 1` labels lie within label distance `m` of the origin label. -/
theorem card_labelDist_le (N : ℕ+) (m : ℕ) :
    (univ.filter fun i : Fin (N : ℕ) => labelDistToOne N i ≤ m).card ≤ 2 * m + 1 := by
  have h := APG.card_cyclic_ball_le (N := N) ⟨0, N.pos⟩ m
  have hfc : (univ.filter fun i : Fin (N : ℕ) => labelDistToOne N i ≤ m) =
      univ.filter fun i : Fin (N : ℕ) => cyclicIndexDistance N ⟨0, N.pos⟩ i ≤ m := by
    apply Finset.filter_congr
    intro i _
    unfold labelDistToOne
    rw [cyclicIndexDistance_comm' N i]
  rw [hfc]
  exact h

end Riesz1
