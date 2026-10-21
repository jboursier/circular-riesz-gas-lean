/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingDisplacementEvent
public import Riesz1.Auxiliary.GradientSplittingConvolutionParticle

/-!
# Labels of a full window and the signed path increments

The quadrature part of Lemma 5.7, full window. For a label `i`
of a full window `{0, …, N-1}`, the path increments `k_{ij}` with `j ≠ i` run once through the
signed set `{k : 0 < |k|, 2|k| < N}`, and, for even `N`, once more through the antipode
`k_{i, j*}` with `j* = (i + N/2) mod N`. This module proves that identity for every function of the
increment.
-/

@[expose] public section

open Finset

namespace Riesz1

noncomputable section

/-- The signed set `{k : 0 < |k|, 2|k| < N}` of nonzero increments with `2|k| < N`, namely
`0 < |k| ≤ (N-1)/2`. -/
def gradFullDiscs (N : ℕ+) : Finset ℤ :=
  (Finset.Icc (-((((N : ℕ) : ℤ) - 1) / 2)) ((((N : ℕ) : ℤ) - 1) / 2)).erase 0

/-- The label `j*` opposite to `i` in a full window, the representative of `i + N/2` in
`{0, …, N-1}`. For even `N` the path from `i` to `j*` is the antipodal one. -/
def gradAntiLabel (N : ℕ+) (i : ℤ) : ℤ :=
  (i + ((N : ℕ) : ℤ) / 2) % ((N : ℕ) : ℤ)

/-- In a full window the path increment is given by the residue `(j - i) mod N`, after unfolding. -/
lemma gradPathIncr_full_eq {ℓ γ : ℝ} {N : ℕ+} (hP : ¬GradPartial N ℓ γ) (i j : ℤ) :
    gradPathIncr N ℓ γ i j =
      if 2 * ((j - i) % ((N : ℕ) : ℤ)) < ((N : ℕ) : ℤ) then (j - i) % ((N : ℕ) : ℤ)
      else if ((N : ℕ) : ℤ) < 2 * ((j - i) % ((N : ℕ) : ℤ))
        then (j - i) % ((N : ℕ) : ℤ) - ((N : ℕ) : ℤ)
      else if i % ((N : ℕ) : ℤ) < j % ((N : ℕ) : ℤ) then ((N : ℕ) : ℤ) / 2
      else -(((N : ℕ) : ℤ) / 2) := by
  unfold gradPathIncr
  simp only [hP, ite_false]

/-- Membership in the signed set: `k ∈ gradFullDiscs N` exactly when `k ≠ 0` and `2|k| < N`. -/
lemma mem_gradFullDiscs {N : ℕ+} {k : ℤ} :
    k ∈ gradFullDiscs N ↔ k ≠ 0 ∧ 2 * |k| < ((N : ℕ) : ℤ) := by
  unfold gradFullDiscs
  rw [Finset.mem_erase, Finset.mem_Icc]
  rcases abs_cases k with ⟨hk, hk0⟩ | ⟨hk, hk0⟩ <;> rw [hk] <;> omega

/-- A bound `-n < 2k < n` gives `2|k| < n`. -/
lemma two_mul_abs_lt_of_bounds {k n : ℤ} (h1 : 2 * k < n) (h2 : -n < 2 * k) : 2 * |k| < n := by
  rcases abs_cases k with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> omega

/-- The linear bounds `-n < 2k < n` of a signed number with `2|k| < n`. -/
lemma two_mul_bounds_of_two_mul_abs_lt {k n : ℤ} (h : 2 * |k| < n) :
    2 * k < n ∧ -n < 2 * k := by
  rcases abs_cases k with ⟨ha, _⟩ | ⟨ha, _⟩ <;> rw [ha] at h <;> constructor <;> omega

/-- The bound `|k| < n` from `2|k| < n`. -/
lemma abs_lt_of_two_mul_abs_lt {k n : ℤ} (h : 2 * |k| < n) : |k| < n := by
  have := abs_nonneg k
  omega

/-- The labels of a full window are the integers `0 ≤ j < N`. -/
lemma mem_gradLabels_full_iff {ℓ γ : ℝ} {N : ℕ+} (hP : ¬GradPartial N ℓ γ) (j : ℤ) :
    j ∈ gradLabels N ℓ γ ↔ 0 ≤ j ∧ j < ((N : ℕ) : ℤ) :=
  mem_gradLabels_full hP j

/-- The residue `(j - i) mod n` is positive for `j ≠ i` in `[0, n)`, and below `n`. -/
lemma emod_sub_pos_of_ne {n i j : ℤ} (hn : 0 < n) (hi0 : 0 ≤ i) (hiN : i < n) (hj0 : 0 ≤ j)
    (hjN : j < n) (hne : j ≠ i) : 0 < (j - i) % n ∧ (j - i) % n < n := by
  refine ⟨?_, Int.emod_lt_of_pos _ hn⟩
  rcases lt_or_gt_of_ne hne with h | h
  · have h1 : (j - i + n * 1) % n = (j - i) % n := Int.add_mul_emod_self_left _ _ _
    have h2 : (j - i + n * 1) % n = j - i + n * 1 := Int.emod_eq_of_lt (by omega) (by omega)
    omega
  · have hr : (j - i) % n = j - i := Int.emod_eq_of_lt (by omega) (by omega)
    omega

/-- The residue of `i + k` seen from `i`: `((i + k) mod n - i) mod n = k mod n`. -/
lemma emod_sub_add_emod (n i k : ℤ) : ((i + k) % n - i) % n = k % n := by
  have h : (i + k) % n - i = k + n * (-((i + k) / n)) := by
    rw [Int.emod_def]
    ring
  rw [h, Int.add_mul_emod_self_left]

/-- The residue `i + (j - i) mod n` is congruent to `j` modulo `n`. -/
lemma emod_add_emod_sub (n i j : ℤ) : (i + (j - i) % n) % n = j % n := by
  have h : i + (j - i) % n = j + n * (-((j - i) / n)) := by
    rw [Int.emod_def]
    ring
  rw [h, Int.add_mul_emod_self_left]

/-- The residue of a signed number with `0 < |k| < n`, as a representative in `[0, n)`. -/
lemma emod_of_signed {n k : ℤ} (hk : k ≠ 0) (hk' : |k| < n) :
    k % n = if 0 < k then k else k + n := by
  rcases lt_or_gt_of_ne hk with h | h
  · have hkn : k % n = (k + n) % n := by
      rw [show k + n = k + n * 1 by ring, Int.add_mul_emod_self_left]
    have hneg : ¬ 0 < k := by omega
    simp only [hneg, ↓reduceIte]
    rw [hkn, Int.emod_eq_of_lt (by rw [abs_of_neg h] at hk'; omega) (by omega)]
  · have hpos : 0 < k := h
    simp only [hpos, ↓reduceIte]
    rw [Int.emod_eq_of_lt (by omega) (by rw [abs_of_pos h] at hk'; exact hk')]

/-- The left inverse: the label `j` of `i + k_{ij}` is recovered modulo `N`. -/
lemma emod_add_pathIncr {ℓ γ : ℝ} {N : ℕ+} (i j : ℤ) :
    (i + gradPathIncr N ℓ γ i j) % ((N : ℕ) : ℤ) = j % ((N : ℕ) : ℤ) := by
  obtain ⟨m, hm⟩ := gradPathIncr_emod N ℓ γ i j
  have h1 : (j - i) % ((N : ℕ) : ℤ) = (j - i) - ((N : ℕ) : ℤ) * ((j - i) / ((N : ℕ) : ℤ)) :=
    Int.emod_def _ _
  have h2 : i + gradPathIncr N ℓ γ i j
      = j + ((N : ℕ) : ℤ) * (m - (j - i) / ((N : ℕ) : ℤ)) := by
    rw [hm, h1]
    ring
  rw [h2, Int.add_mul_emod_self_left]

/-- The increment of a path from `i` to `j` with `j ≠ i` in `[0, N)` and `2 · residue ≠ N`
lies in the signed set. -/
lemma gradPathIncr_mem_discs {ℓ γ : ℝ} {N : ℕ+} (hP : ¬GradPartial N ℓ γ) {i j : ℤ}
    (hn : (0 : ℤ) < ((N : ℕ) : ℤ)) (hi0 : 0 ≤ i) (hiN : i < ((N : ℕ) : ℤ))
    (hj0 : 0 ≤ j) (hjN : j < ((N : ℕ) : ℤ)) (hne : j ≠ i)
    (hanti : 2 * ((j - i) % ((N : ℕ) : ℤ)) ≠ ((N : ℕ) : ℤ)) :
    gradPathIncr N ℓ γ i j ∈ gradFullDiscs N := by
  obtain ⟨hr0, hrN⟩ := emod_sub_pos_of_ne hn hi0 hiN hj0 hjN hne
  rw [mem_gradFullDiscs, gradPathIncr_full_eq hP]
  split_ifs with h1 h2 h3
  · exact ⟨by omega, two_mul_abs_lt_of_bounds h1 (by omega)⟩
  · exact ⟨by omega, two_mul_abs_lt_of_bounds (by omega) (by omega)⟩
  · omega
  · omega

/-- The residue map is a bijection from the nonantipodal labels onto the signed set: the image
`(i + k) mod N` of a signed increment is a label different from `i` and nonantipodal. -/
lemma emod_add_mem_erase_nonanti {ℓ γ : ℝ} {N : ℕ+} (hP : ¬GradPartial N ℓ γ)
    {i k : ℤ} (hn : (0 : ℤ) < ((N : ℕ) : ℤ)) (hk : k ∈ gradFullDiscs N) :
    (i + k) % ((N : ℕ) : ℤ) ∈ ((gradLabels N ℓ γ).erase i) ∧
      2 * (((i + k) % ((N : ℕ) : ℤ) - i) % ((N : ℕ) : ℤ)) ≠ ((N : ℕ) : ℤ) := by
  obtain ⟨hk0, hk2⟩ := mem_gradFullDiscs.mp hk
  obtain ⟨hl1, hl2⟩ := two_mul_bounds_of_two_mul_abs_lt hk2
  have hkn : |k| < ((N : ℕ) : ℤ) := abs_lt_of_two_mul_abs_lt hk2
  have hres : ((i + k) % ((N : ℕ) : ℤ) - i) % ((N : ℕ) : ℤ) = k % ((N : ℕ) : ℤ) :=
    emod_sub_add_emod _ _ _
  have hkmod : k % ((N : ℕ) : ℤ) = if 0 < k then k else k + ((N : ℕ) : ℤ) :=
    emod_of_signed hk0 hkn
  have hmem : (i + k) % ((N : ℕ) : ℤ) ∈ gradLabels N ℓ γ := by
    rw [mem_gradLabels_full hP]
    exact ⟨Int.emod_nonneg _ hn.ne', Int.emod_lt_of_pos _ hn⟩
  refine ⟨Finset.mem_erase.mpr ⟨?_, hmem⟩, ?_⟩
  · intro hcontra
    have h0 : k % ((N : ℕ) : ℤ) = 0 := by
      rw [← hres, hcontra, sub_self, Int.zero_emod]
    rw [hkmod] at h0
    split_ifs at h0 <;> omega
  · rw [hres, hkmod]
    split_ifs <;> omega

/-- The left inverse on the nonantipodal labels: `(i + k_{ij}) mod N = j`. -/
lemma emod_add_pathIncr_of_mem {ℓ γ : ℝ} {N : ℕ+} (hP : ¬GradPartial N ℓ γ) {i j : ℤ}
    (hj : j ∈ gradLabels N ℓ γ) : (i + gradPathIncr N ℓ γ i j) % ((N : ℕ) : ℤ) = j := by
  rw [emod_add_pathIncr, Int.emod_eq_of_lt ((mem_gradLabels_full_iff hP j).mp hj).1
    ((mem_gradLabels_full_iff hP j).mp hj).2]

/-- The right inverse: the increment of the path from `i` to `(i + k) mod N` is `k`, for a
signed increment `k` with `2|k| < N`. -/
lemma gradPathIncr_mod_of_mem {ℓ γ : ℝ} {N : ℕ+} (hP : ¬GradPartial N ℓ γ) {i k : ℤ}
    (hk : k ∈ gradFullDiscs N) :
    gradPathIncr N ℓ γ i ((i + k) % ((N : ℕ) : ℤ)) = k := by
  have hn : (0 : ℤ) < ((N : ℕ) : ℤ) := by exact_mod_cast N.pos
  obtain ⟨hk0, hk2⟩ := mem_gradFullDiscs.mp hk
  obtain ⟨hl1, hl2⟩ := two_mul_bounds_of_two_mul_abs_lt hk2
  have hk' : |k| < ((N : ℕ) : ℤ) := abs_lt_of_two_mul_abs_lt hk2
  rw [gradPathIncr_full_eq hP, emod_sub_add_emod, emod_of_signed hk0 hk']
  split_ifs <;> omega

/-- The antipodal label `j*` has residue `N/2` from `i`, for even `N`. -/
lemma emod_anti_sub {N : ℕ+} (i : ℤ) (heven : (N : ℕ) % 2 = 0) :
    ((gradAntiLabel N i) - i) % ((N : ℕ) : ℤ) = ((N : ℕ) : ℤ) / 2 := by
  have hn : (0 : ℤ) < ((N : ℕ) : ℤ) := by exact_mod_cast N.pos
  unfold gradAntiLabel
  rw [emod_sub_add_emod, Int.emod_eq_of_lt (by omega) (by omega)]

/-- The sum over the labels `j ≠ i` of a function of the increment, as a sum over the signed set
plus, for even `N`, one antipodal term (quadrature part of Lemma 5.7). -/
theorem sum_labels_erase_full {ℓ γ : ℝ} {N : ℕ+} (hP : ¬GradPartial N ℓ γ) {i : ℤ}
    (hi : i ∈ gradLabels N ℓ γ) (F : ℤ → ℝ) :
    ∑ j ∈ (gradLabels N ℓ γ).erase i, F (gradPathIncr N ℓ γ i j)
      = ∑ k ∈ gradFullDiscs N, F k
        + if (N : ℕ) % 2 = 0 then F (gradPathIncr N ℓ γ i (gradAntiLabel N i)) else 0 := by
  have hn : (0 : ℤ) < ((N : ℕ) : ℤ) := by exact_mod_cast N.pos
  obtain ⟨hi0, hiN⟩ := (mem_gradLabels_full_iff hP i).mp hi
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun j : ℤ => 2 * ((j - i) % ((N : ℕ) : ℤ)) = ((N : ℕ) : ℤ)),
    add_comm]
  congr 1
  · refine Finset.sum_nbij' (fun j => gradPathIncr N ℓ γ i j) (fun k => (i + k) % ((N : ℕ) : ℤ))
      ?_ ?_ ?_ ?_ ?_
    · intro j hj
      rw [Finset.mem_filter, Finset.mem_erase] at hj
      obtain ⟨⟨hne, hjl⟩, hanti⟩ := hj
      obtain ⟨hj0, hjN⟩ := (mem_gradLabels_full_iff hP j).mp hjl
      exact gradPathIncr_mem_discs hP hn hi0 hiN hj0 hjN hne (by simpa using hanti)
    · intro k hk
      rw [Finset.mem_filter, Finset.mem_erase]
      obtain ⟨hmem, hanti⟩ := emod_add_mem_erase_nonanti hP hn hk
      exact ⟨Finset.mem_erase.mp hmem, by simpa using hanti⟩
    · intro j hj
      rw [Finset.mem_filter] at hj
      exact emod_add_pathIncr_of_mem hP (Finset.mem_of_mem_erase hj.1)
    · intro k hk
      exact gradPathIncr_mod_of_mem hP hk
    · intro j hj
      rfl
  · split_ifs with heven
    · have hfilt : (((gradLabels N ℓ γ).erase i).filter
          (fun j : ℤ => 2 * ((j - i) % ((N : ℕ) : ℤ)) = ((N : ℕ) : ℤ))) =
          {gradAntiLabel N i} := by
        have hN2 : 2 ≤ (N : ℕ) := by have := N.pos; omega
        ext j
        simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_singleton,
          mem_gradLabels_full_iff hP]
        constructor
        · rintro ⟨⟨hne, hj0, hjN⟩, hr⟩
          have hres : (j - i) % ((N : ℕ) : ℤ) = ((N : ℕ) : ℤ) / 2 := by omega
          unfold gradAntiLabel
          rw [← hres, emod_add_emod_sub, Int.emod_eq_of_lt hj0 hjN]
        · rintro rfl
          have hanti := emod_anti_sub (N := N) i heven
          have hpos : ((N : ℕ) : ℤ) / 2 ≠ 0 := by omega
          refine ⟨⟨?_, Int.emod_nonneg _ hn.ne', Int.emod_lt_of_pos _ hn⟩, ?_⟩
          · intro hcontra
            rw [hcontra, sub_self, Int.zero_emod] at hanti
            exact hpos hanti.symm
          · rw [hanti]
            omega
      rw [hfilt, Finset.sum_singleton]
    · have hfilt : (((gradLabels N ℓ γ).erase i).filter
          (fun j : ℤ => 2 * ((j - i) % ((N : ℕ) : ℤ)) = ((N : ℕ) : ℤ))) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro j _ hj
        omega
      rw [hfilt, Finset.sum_empty]

/-- Odd cancellation on the signed set: a function odd on `gradFullDiscs` sums to zero there. -/
theorem sum_gradFullDiscs_eq_zero {N : ℕ+} (F : ℤ → ℝ)
    (hF : ∀ k ∈ gradFullDiscs N, F (-k) = -F k) :
    ∑ k ∈ gradFullDiscs N, F k = 0 := by
  refine Finset.sum_involution (fun k _ => -k) ?_ ?_ ?_ ?_
  · intro a ha
    rw [hF a ha]
    ring
  · intro a ha _ h
    have ha0 := (mem_gradFullDiscs.mp ha).1
    omega
  · intro a ha
    obtain ⟨h1, h2⟩ := mem_gradFullDiscs.mp ha
    rw [mem_gradFullDiscs]
    exact ⟨by omega, by rw [abs_neg]; exact h2⟩
  · intro a _
    ring

/-- For even `N`, the path from `i` to its antipodal label is `±N/2`. -/
lemma gradPathIncr_anti_eq {ℓ γ : ℝ} {N : ℕ+} (hP : ¬GradPartial N ℓ γ) {i : ℤ}
    (heven : (N : ℕ) % 2 = 0) :
    gradPathIncr N ℓ γ i (gradAntiLabel N i) = ((N : ℕ) : ℤ) / 2 ∨
      gradPathIncr N ℓ γ i (gradAntiLabel N i) = -(((N : ℕ) : ℤ) / 2) := by
  rw [gradPathIncr_full_eq hP, emod_anti_sub i heven]
  split_ifs <;> omega

/-- The sum over the labels `j ≠ i` of a nonnegative function of the residue `(j - i) mod N` is
at most the sum over all residues `0 ≤ r < N` (the sum over a set of residues is injective). -/
lemma sum_erase_residue_le {ℓ γ : ℝ} {N : ℕ+} (hP : ¬GradPartial N ℓ γ) {i : ℤ}
    (hi : i ∈ gradLabels N ℓ γ) (G : ℕ → ℝ) (hG : ∀ r, 0 ≤ G r) :
    ∑ j ∈ (gradLabels N ℓ γ).erase i, G (((j - i) % ((N : ℕ) : ℤ)).toNat)
      ≤ ∑ r ∈ Finset.range (N : ℕ), G r := by
  have hn : (0 : ℤ) < ((N : ℕ) : ℤ) := by exact_mod_cast N.pos
  obtain ⟨hi0, hiN⟩ := (mem_gradLabels_full_iff hP i).mp hi
  have hbound : ∀ j ∈ (gradLabels N ℓ γ).erase i,
      0 ≤ (j - i) % ((N : ℕ) : ℤ) ∧ (j - i) % ((N : ℕ) : ℤ) < ((N : ℕ) : ℤ) := by
    intro j hj
    obtain ⟨hne, hjl⟩ := Finset.mem_erase.mp hj
    obtain ⟨hj0, hjN⟩ := (mem_gradLabels_full_iff hP j).mp hjl
    have := emod_sub_pos_of_ne hn hi0 hiN hj0 hjN hne
    exact ⟨by omega, this.2⟩
  have hinj : Set.InjOn (fun j : ℤ => ((j - i) % ((N : ℕ) : ℤ)).toNat)
      ((gradLabels N ℓ γ).erase i : Set ℤ) := by
    intro j1 hj1 j2 hj2 heq
    have h1 := hbound j1 hj1
    have h2 := hbound j2 hj2
    have heq' : (j1 - i) % ((N : ℕ) : ℤ) = (j2 - i) % ((N : ℕ) : ℤ) := by
      simp only at heq
      omega
    have hl1 := (mem_gradLabels_full_iff hP j1).mp (Finset.mem_of_mem_erase hj1)
    have hl2 := (mem_gradLabels_full_iff hP j2).mp (Finset.mem_of_mem_erase hj2)
    have hmod : j1 % ((N : ℕ) : ℤ) = j2 % ((N : ℕ) : ℤ) := by
      rw [← emod_add_emod_sub ((N : ℕ) : ℤ) i j1, ← emod_add_emod_sub ((N : ℕ) : ℤ) i j2, heq']
    rw [Int.emod_eq_of_lt hl1.1 hl1.2, Int.emod_eq_of_lt hl2.1 hl2.2] at hmod
    exact hmod
  rw [← Finset.sum_image (f := G) (g := fun j : ℤ => ((j - i) % ((N : ℕ) : ℤ)).toNat) hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun r _ _ => hG r)
  intro r hr
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hr
  rw [Finset.mem_range]
  have := hbound j hj
  omega

end

end Riesz1
