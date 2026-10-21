/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriGoodGradientDefs

/-!
# Counting the pairs whose arc contains a label

Part of Lemma 5.2 (the good-event part), gradient claim. The derivative of the good-event cutoff
in the gap coordinate `z_i` is a sum over the pairs `p = (a, k)` whose oriented arc from `a` to
`a + k` contains the label `i`. This file proves the two counting facts behind the bound.

* The pairs of `cutoffPairs N (window N K γ)` have `|k| ≤ ⌊4 K^γ⌋₊` (`gradient_pair_bound`). In the
  full case this uses `N ≤ 8 K^γ`. In the partial case the cyclic constraint `labelOf (a + k) ∈ I`
  forces `k = b - a` for two integers `a, b` in `[-M, M]`, so `|k| ≤ 2 M`.
* For a label `i`, at most `(2m + 1) m` pairs with `|k| ≤ m` have a nonzero oriented arc sum at the
  unit vector `e_i` (`gradient_card_arc_ne_zero`). Each such pair has `|k| ≤ m` and is determined
  by the label `i - (r - a)` for a label `r` of its arc.
-/

@[expose] public section

noncomputable section

open Finset MeasureTheory

namespace Riesz1

/-! ### Labels modulo `N` -/

/-- Two integers have the same label exactly when they are congruent modulo `N`. -/
theorem labelOf_eq_iff_emod (N : ℕ+) (x y : ℤ) :
    labelOf N x = labelOf N y ↔ x % ((N : ℕ) : ℤ) = y % ((N : ℕ) : ℤ) := by
  constructor
  · intro h
    have h' := congrArg (fun f : Fin (N : ℕ) => ((f : ℕ) : ℤ)) h
    simp only [labelOf_val_int] at h'
    exact h'
  · intro h
    apply Fin.ext
    have h' : ((labelOf N x : ℕ) : ℤ) = ((labelOf N y : ℕ) : ℤ) := by
      rw [labelOf_val_int, labelOf_val_int, h]
    exact_mod_cast h'

/-- Integers differing by a multiple of `N` have the same label. -/
theorem labelOf_eq_of_dvd (N : ℕ+) {x y : ℤ} (h : ((N : ℕ) : ℤ) ∣ y - x) :
    labelOf N x = labelOf N y :=
  (labelOf_eq_iff_emod N x y).2 (Int.modEq_iff_dvd.2 h)

/-- Equal labels give a difference divisible by `N`. -/
theorem dvd_of_labelOf_eq (N : ℕ+) {x y : ℤ} (h : labelOf N x = labelOf N y) :
    ((N : ℕ) : ℤ) ∣ y - x :=
  Int.modEq_iff_dvd.1 ((labelOf_eq_iff_emod N x y).1 h)

/-! ### The pair lengths -/

/-- **Pair lengths.** For `K ≥ 1` and `γ ≥ 0`, every pair `(i, k)` of the good-event cutoff
satisfies `|k| ≤ ⌊4 K^γ⌋₊`. -/
theorem gradient_pair_bound {K γ : ℝ} (hK : 1 ≤ K) (hγ : 0 ≤ γ) (N : ℕ+) :
    ∀ p ∈ cutoffPairs N (window N K γ),
      -((⌊4 * K ^ γ⌋₊ : ℕ) : ℤ) ≤ p.2 ∧ p.2 ≤ ((⌊4 * K ^ γ⌋₊ : ℕ) : ℤ) := by
  intro p hp
  have hmem := Finset.mem_filter.1 hp
  have hkIcc : p.2 ∈ Icc (-((((N : ℕ) / 2 : ℕ)) : ℤ)) ((((N : ℕ) / 2 : ℕ)) : ℤ) :=
    (Finset.mem_erase.1 (Finset.mem_product.1 hmem.1).2).2
  rw [Finset.mem_Icc] at hkIcc
  have hKγ : 1 ≤ K ^ γ := Real.one_le_rpow hK hγ
  have hK0 : 0 ≤ K ^ γ := by linarith
  by_cases hpart : K ^ γ < ((N : ℕ) : ℝ) / 8
  · -- Partial window: the labels of `p.1` and `p.1 + p.2` lie in `[-M, M]` for `M = ⌊K^γ⌋₊`.
    have hw := window_partial hK0 hpart
    have h8 : 8 * ⌊K ^ γ⌋₊ < (N : ℕ) := by
      have hfl : (⌊K ^ γ⌋₊ : ℝ) ≤ K ^ γ := Nat.floor_le hK0
      have hlt : (8 : ℝ) * K ^ γ < ((N : ℕ) : ℝ) := by linarith
      have : (8 : ℝ) * ⌊K ^ γ⌋₊ < ((N : ℕ) : ℝ) := by linarith
      exact_mod_cast this
    have hM2 : 2 * ⌊K ^ γ⌋₊ ≤ ⌊4 * K ^ γ⌋₊ := by
      apply Nat.le_floor
      have hfl : (⌊K ^ γ⌋₊ : ℝ) ≤ K ^ γ := Nat.floor_le hK0
      push_cast
      linarith
    have hpi : p.1 ∈ window N K γ := hmem.2.1
    have hpk : labelOf N (((p.1 : ℕ) : ℤ) + p.2) ∈ window N K γ := hmem.2.2
    rw [hw] at hpi hpk
    obtain ⟨a, ha, hae⟩ := Finset.mem_image.1 hpi
    obtain ⟨b, hb, hbe⟩ := Finset.mem_image.1 hpk
    rw [Finset.mem_Icc] at ha hb
    -- Both `p.1 - a` and `p.1 + p.2 - b` are divisible by `N`.
    have hA : ((N : ℕ) : ℤ) ∣ ((p.1 : ℕ) : ℤ) - a :=
      dvd_of_labelOf_eq N (hae.trans (labelOf_natCast N p.1).symm)
    have hB : ((N : ℕ) : ℤ) ∣ (((p.1 : ℕ) : ℤ) + p.2) - b := dvd_of_labelOf_eq N hbe
    have hd : ((N : ℕ) : ℤ) ∣ p.2 - (b - a) := by
      have h := dvd_sub hB hA
      have e : (((p.1 : ℕ) : ℤ) + p.2 - b) - (((p.1 : ℕ) : ℤ) - a) = p.2 - (b - a) := by ring
      rwa [e] at h
    have hlt : |p.2 - (b - a)| < ((N : ℕ) : ℤ) := by
      rw [abs_lt]
      constructor <;> omega
    have hzero : p.2 - (b - a) = 0 := Int.eq_zero_of_abs_lt_dvd hd hlt
    constructor <;> omega
  · -- Full window: every label lies in the window, and `N ≤ 8 K^γ`.
    have hfull' : ((N : ℕ) : ℝ) ≤ 8 * K ^ γ := by
      have := not_lt.1 hpart
      linarith
    have hhalf : ((((N : ℕ) / 2 : ℕ)) : ℝ) ≤ 4 * K ^ γ := by
      have h2 : 2 * ((N : ℕ) / 2) ≤ (N : ℕ) := Nat.mul_div_le _ _
      have h2R : (2 : ℝ) * ((((N : ℕ) / 2 : ℕ)) : ℝ) ≤ ((N : ℕ) : ℝ) := by
        exact_mod_cast h2
      linarith
    have hm : (N : ℕ) / 2 ≤ ⌊4 * K ^ γ⌋₊ := Nat.le_floor hhalf
    constructor <;> omega

/-! ### Arcs at a label -/

/-- A sum of indicators of one label over a set of integers. -/
theorem sum_single_Ico_mem_unit (N : ℕ+) (i : Fin (N : ℕ)) (c d : ℤ)
    (hlen : |d - c| < ((N : ℕ) : ℤ)) :
    0 ≤ ∑ r ∈ Ico c d, (Pi.single i (1 : ℝ) : Fin (N : ℕ) → ℝ) (labelOf N r) ∧
      ∑ r ∈ Ico c d, (Pi.single i (1 : ℝ) : Fin (N : ℕ) → ℝ) (labelOf N r) ≤ 1 := by
  classical
  have hsum : ∑ r ∈ Ico c d, (Pi.single i (1 : ℝ) : Fin (N : ℕ) → ℝ) (labelOf N r) =
      ((Ico c d).filter fun r => labelOf N r = i).card := by
    rw [← Finset.sum_boole]
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases h : labelOf N r = i <;> simp [h]
  rw [hsum]
  have hcard : ((Ico c d).filter fun r => labelOf N r = i).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    rw [Finset.mem_filter, Finset.mem_Ico] at hx hy
    have hdvd : ((N : ℕ) : ℤ) ∣ y - x :=
      dvd_of_labelOf_eq N (hx.2.trans hy.2.symm)
    have hl := abs_lt.1 hlen
    have hxy : |y - x| < ((N : ℕ) : ℤ) := by
      rw [abs_lt]
      constructor <;> omega
    exact (sub_eq_zero.1 (Int.eq_zero_of_abs_lt_dvd hdvd hxy)).symm
  constructor
  · exact Nat.cast_nonneg _
  · exact_mod_cast hcard

/-- The oriented arc sum of a unit vector is at most one in absolute value, when the arc has
fewer than `N` labels. -/
theorem abs_gapOrientedSum_single_le (N : ℕ+) (i : Fin (N : ℕ)) (a b : ℤ)
    (hlen : |b - a| < ((N : ℕ) : ℤ)) :
    |gapOrientedSum N (Pi.single i (1 : ℝ)) a b| ≤ 1 := by
  unfold gapOrientedSum
  have h1 := sum_single_Ico_mem_unit N i a b hlen
  have h2 := sum_single_Ico_mem_unit N i b a (by rwa [abs_sub_comm])
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- The oriented arc sum of a unit vector vanishes when the arc avoids the label `i`. -/
theorem gapOrientedSum_single_eq_zero (N : ℕ+) (i : Fin (N : ℕ)) (a b : ℤ)
    (h : ∀ r ∈ Ico a b ∪ Ico b a, labelOf N r ≠ i) :
    gapOrientedSum N (Pi.single i (1 : ℝ)) a b = 0 := by
  unfold gapOrientedSum
  have h1 : ∑ r ∈ Ico a b, (Pi.single i (1 : ℝ) : Fin (N : ℕ) → ℝ) (labelOf N r) = 0 := by
    refine Finset.sum_eq_zero fun r hr => ?_
    simp [h r (Finset.mem_union_left _ hr)]
  have h2 : ∑ r ∈ Ico b a, (Pi.single i (1 : ℝ) : Fin (N : ℕ) → ℝ) (labelOf N r) = 0 := by
    refine Finset.sum_eq_zero fun r hr => ?_
    simp [h r (Finset.mem_union_right _ hr)]
  rw [h1, h2, sub_zero]

/-! ### The count of pairs with a nonzero arc sum -/

/-- **Count of arcs through a label.** Let `P` be a finite set of pairs `(a, k)` with
`|k| ≤ m`. The pairs of `P` whose oriented arc sum at the unit vector `e_i` is nonzero number at
most `(2 m + 1) m`. -/
theorem gradient_card_arc_ne_zero (N : ℕ+) (i : Fin (N : ℕ)) (P : Finset (Fin (N : ℕ) × ℤ))
    (m : ℕ) (hP : ∀ p ∈ P, -(m : ℤ) ≤ p.2 ∧ p.2 ≤ (m : ℤ)) :
    (P.filter fun p => gapOrientedSum N (Pi.single i (1 : ℝ))
        (((p.1 : ℕ) : ℤ)) (((p.1 : ℕ) : ℤ) + p.2) ≠ 0).card ≤ (2 * m + 1) * m := by
  classical
  set Q := P.filter fun p => gapOrientedSum N (Pi.single i (1 : ℝ))
      (((p.1 : ℕ) : ℤ)) (((p.1 : ℕ) : ℤ) + p.2) ≠ 0 with hQ
  have hsub : Q ⊆ (Icc (-(m : ℤ)) (m : ℤ)).biUnion fun k =>
      (Ico (min 0 k) (max 0 k)).image fun u => (labelOf N (((i : ℕ) : ℤ) - u), k) := by
    intro p hp
    obtain ⟨hpP, hne⟩ := Finset.mem_filter.1 hp
    have hk := hP p hpP
    rw [Finset.mem_biUnion]
    refine ⟨p.2, Finset.mem_Icc.2 hk, ?_⟩
    -- Some label `r` of the arc of `p` equals `i`.
    have hr : ∃ r ∈ Ico (((p.1 : ℕ) : ℤ)) (((p.1 : ℕ) : ℤ) + p.2) ∪
        Ico (((p.1 : ℕ) : ℤ) + p.2) (((p.1 : ℕ) : ℤ)), labelOf N r = i := by
      by_contra hcon
      push Not at hcon
      exact hne (gapOrientedSum_single_eq_zero N i _ _ hcon)
    obtain ⟨r, hrmem, hri⟩ := hr
    have hdiv : ((N : ℕ) : ℤ) ∣ (((i : ℕ) : ℤ)) - r :=
      dvd_of_labelOf_eq N (hri.trans (labelOf_natCast N i).symm)
    rw [Finset.mem_image]
    refine ⟨r - ((p.1 : ℕ) : ℤ), ?_, ?_⟩
    · rw [Finset.mem_union, Finset.mem_Ico, Finset.mem_Ico] at hrmem
      rw [Finset.mem_Ico, max_def, min_def]
      split_ifs <;> omega
    · apply Prod.ext
      · refine Eq.trans (labelOf_eq_of_dvd N ?_) (labelOf_natCast N p.1)
        have e : ((p.1 : ℕ) : ℤ) - (((i : ℕ) : ℤ) - (r - ((p.1 : ℕ) : ℤ))) =
            -((((i : ℕ) : ℤ)) - r) := by ring
        rw [e]
        exact dvd_neg.2 hdiv
      · rfl
  have hcard : Q.card ≤ (2 * m + 1) * m := by
    calc Q.card
        ≤ ((Icc (-(m : ℤ)) (m : ℤ)).biUnion fun k =>
            (Ico (min 0 k) (max 0 k)).image fun u => (labelOf N (((i : ℕ) : ℤ) - u), k)).card :=
          card_le_card hsub
      _ ≤ ∑ k ∈ Icc (-(m : ℤ)) (m : ℤ),
            ((Ico (min 0 k) (max 0 k)).image fun u => (labelOf N (((i : ℕ) : ℤ) - u), k)).card :=
          card_biUnion_le
      _ ≤ ∑ _k ∈ Icc (-(m : ℤ)) (m : ℤ), m := by
          refine Finset.sum_le_sum fun k hk => ?_
          rw [Finset.mem_Icc] at hk
          refine (card_image_le).trans ?_
          rw [Int.card_Ico]
          have hw : max 0 k - min 0 k ≤ (m : ℤ) := by
            rw [max_def, min_def]
            split_ifs <;> omega
          omega
      _ = (2 * m + 1) * m := by
          rw [Finset.sum_const, Int.card_Icc, smul_eq_mul]
          congr 1
          omega
  exact hcard

end Riesz1

end
end
