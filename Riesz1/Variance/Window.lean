/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Frozen.CyclicIndexDistance
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Finset.Card

/-!
# Windows of labels for the nearest-neighbour forcing

The paper labels particles `1, …, N`. Here the paper's label `i` is the
index `i - 1` in `Fin N`, so the distance `d(i, 1)` is `cyclicIndexDistance N i 0`.
Cyclic lifts are indexed from zero as in `Riesz1.cyclicLift`.

* `windowTime N K γ` is the time `t_γ`: `K^γ / N` in the partial case `K^γ < N / 8`, and `1 / 2`
  otherwise.
* `windowLabels N t` is the set of labels with `d(i, 1) ≤ N t`. The window `I_γ` is
  `window N K γ = windowLabels N (windowTime N K γ)`.
* In the full case the window is every label, each once (`window_full`). In the partial case it is
  the set of residues of the integers `k` with `|k| ≤ ⌊K^γ⌋` (`window_partial`), which are the
  consecutive representatives `1 - ⌊K^γ⌋, …, 1 + ⌊K^γ⌋` of the paper, shifted to indices.
* `nearestPairs N I` is the set of labels `i ∈ I` whose next label `i + 1`, modulo `N`, also lies in
  `I`. The nearest-neighbour sum runs over these pairs.

The count `#(windowLabels N t) ≤ 2 ⌊N t⌋ + 1` and `#(nearestPairs N (window N K γ)) ≤ 8 K^γ` are
the counting inputs of the total variation bound.
-/

@[expose] public section

open Finset

namespace Riesz1

/-- The distance `d(i, 1)`, with the paper's label `1` at the index `0`. -/
def labelDistToOne (N : ℕ+) (i : Fin (N : ℕ)) : ℕ :=
  cyclicIndexDistance N i ⟨0, N.pos⟩

/-- The label of the integer `n` in `Fin N`: the residue of `n` modulo `N`, in `{0, …, N - 1}`. -/
def labelOf (N : ℕ+) (n : ℤ) : Fin (N : ℕ) :=
  ⟨(n % (N : ℕ)).toNat, by
    have h := Int.emod_lt_of_pos n (show (0 : ℤ) < (N : ℕ) by exact_mod_cast N.pos)
    exact_mod_cast (Int.toNat_lt (Int.emod_nonneg n (by exact_mod_cast N.ne_zero))).mpr h⟩

/-- The window time `t_γ`: `K^γ / N` when `K^γ < N / 8`, and `1 / 2` otherwise. -/
noncomputable def windowTime (N : ℕ+) (K γ : ℝ) : ℝ :=
  if K ^ γ < ((N : ℕ) : ℝ) / 8 then K ^ γ / ((N : ℕ) : ℝ) else 1 / 2

/-- The labels `i` with `d(i, 1) ≤ N t`. -/
noncomputable def windowLabels (N : ℕ+) (t : ℝ) : Finset (Fin (N : ℕ)) :=
  univ.filter fun i => (labelDistToOne N i : ℝ) ≤ ((N : ℕ) : ℝ) * t

/-- The window `I_γ`, for the scale `K` and the exponent `γ`. -/
noncomputable def window (N : ℕ+) (K γ : ℝ) : Finset (Fin (N : ℕ)) :=
  windowLabels N (windowTime N K γ)

/-- The next label `i + 1`, taken modulo `N`. -/
def nextLabel (N : ℕ+) (i : Fin (N : ℕ)) : Fin (N : ℕ) :=
  ⟨(i.val + 1) % (N : ℕ), Nat.mod_lt _ N.pos⟩

/-- The nearest-neighbour pairs `(i, i + 1)` with both labels in `I`, indexed by `i`. -/
def nearestPairs (N : ℕ+) (I : Finset (Fin (N : ℕ))) : Finset (Fin (N : ℕ)) :=
  I.filter fun i => nextLabel N i ∈ I

/-! ### The time `t_γ` -/

/-- In the partial case the window time is `K^γ / N`. -/
theorem windowTime_of_lt {N : ℕ+} {K γ : ℝ} (h : K ^ γ < ((N : ℕ) : ℝ) / 8) :
    windowTime N K γ = K ^ γ / ((N : ℕ) : ℝ) := by
  simp [windowTime, h]

/-- Otherwise the window time is `1 / 2`, which is the full case. -/
theorem windowTime_of_not_lt {N : ℕ+} {K γ : ℝ} (h : ¬ K ^ γ < ((N : ℕ) : ℝ) / 8) :
    windowTime N K γ = 1 / 2 := by
  simp [windowTime, h]

/-! ### The distance to label one -/

/-- The distance `d(i, 1)` is the minimum of `i` and `N - i`, the two arcs from the label one. -/
theorem labelDistToOne_eq (N : ℕ+) (i : Fin (N : ℕ)) :
    labelDistToOne N i = min i.val ((N : ℕ) - i.val) := by
  simp [labelDistToOne, cyclicIndexDistance, Nat.dist_zero_right]

/-- Every label has `d(i, 1) ≤ N / 2`. -/
theorem labelDistToOne_le_half (N : ℕ+) (i : Fin (N : ℕ)) :
    (labelDistToOne N i : ℝ) ≤ ((N : ℕ) : ℝ) / 2 := by
  have h : 2 * labelDistToOne N i ≤ (N : ℕ) := by
    rw [labelDistToOne_eq]
    have := i.isLt
    omega
  have hr : (2 : ℝ) * (labelDistToOne N i : ℝ) ≤ ((N : ℕ) : ℝ) := by exact_mod_cast h
  linarith

/-- In the full case every label lies in the window, so the window is all of `Fin N`: each label
occurs once. -/
theorem window_full {N : ℕ+} {K γ : ℝ} (h : ¬ K ^ γ < ((N : ℕ) : ℝ) / 8) :
    window N K γ = univ := by
  unfold window windowLabels
  rw [windowTime_of_not_lt h]
  refine filter_true_of_mem fun i _ => ?_
  have := labelDistToOne_le_half N i
  linarith

/-! ### The label map -/

/-- The label of a natural index: `labelOf N i = i` for `i < N`. -/
theorem labelOf_natCast (N : ℕ+) (i : Fin (N : ℕ)) : labelOf N (i.val : ℤ) = i := by
  apply Fin.ext
  unfold labelOf
  simp only
  rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast i.isLt), Int.toNat_natCast]

/-- The label of `i - N` is `i`, for `i < N`: the integers `i` and `i - N` have the same residue. -/
theorem labelOf_natCast_sub (N : ℕ+) (i : Fin (N : ℕ)) :
    labelOf N ((i.val : ℤ) - (N : ℕ)) = i := by
  apply Fin.ext
  unfold labelOf
  simp only
  rw [show (i.val : ℤ) - (N : ℕ) = (i.val : ℤ) + (N : ℕ) * (-1) by ring,
    Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast i.isLt),
    Int.toNat_natCast]

/-- The labels of `windowLabels N t` are residues of integers in `[-M, M]`, where `M = ⌊N t⌋`.
A label with `d(i, 1) ≤ M` is the residue of `i` (when `i ≤ M`) or of `i - N` (otherwise). -/
theorem windowLabels_subset_image (N : ℕ+) (t : ℝ) :
    windowLabels N t ⊆
      (Icc (-(⌊((N : ℕ) : ℝ) * t⌋₊ : ℤ)) (⌊((N : ℕ) : ℝ) * t⌋₊ : ℤ)).image (labelOf N) := by
  intro i hi
  have hd : labelDistToOne N i ≤ ⌊((N : ℕ) : ℝ) * t⌋₊ := Nat.le_floor (mem_filter.1 hi).2
  rw [labelDistToOne_eq] at hd
  have hi' := i.isLt
  rw [mem_image]
  by_cases h : i.val ≤ ⌊((N : ℕ) : ℝ) * t⌋₊
  · refine ⟨(i.val : ℤ), ?_, labelOf_natCast N i⟩
    rw [mem_Icc]
    constructor <;> omega
  · refine ⟨(i.val : ℤ) - (N : ℕ), ?_, labelOf_natCast_sub N i⟩
    rw [mem_Icc]
    constructor <;> omega

/-! ### Counting -/

/-- The window `windowLabels N t` has at most `2 ⌊N t⌋ + 1` labels. -/
theorem card_windowLabels_le (N : ℕ+) (t : ℝ) :
    (windowLabels N t).card ≤ 2 * ⌊((N : ℕ) : ℝ) * t⌋₊ + 1 := by
  calc (windowLabels N t).card
      ≤ ((Icc (-(⌊((N : ℕ) : ℝ) * t⌋₊ : ℤ)) (⌊((N : ℕ) : ℝ) * t⌋₊ : ℤ)).image
          (labelOf N)).card := card_le_card (windowLabels_subset_image N t)
    _ ≤ (Icc (-(⌊((N : ℕ) : ℝ) * t⌋₊ : ℤ)) (⌊((N : ℕ) : ℝ) * t⌋₊ : ℤ)).card := card_image_le
    _ = 2 * ⌊((N : ℕ) : ℝ) * t⌋₊ + 1 := by rw [Int.card_Icc]; omega

/-! ### The partial window -/

/-- For an integer `k` with `|k| ≤ M` and `8 M < N`, the label of `k` lies within distance `M`
of label one. Its residue is `k` when `k ≥ 0` and `k + N` when `k < 0`. -/
theorem labelDistToOne_labelOf_le {N : ℕ+} {M : ℕ} (hM : 8 * M < N) {k : ℤ}
    (hk₁ : -(M : ℤ) ≤ k) (hk₂ : k ≤ (M : ℤ)) :
    labelDistToOne N (labelOf N k) ≤ M := by
  have hN : (0 : ℤ) < (N : ℕ) := by exact_mod_cast N.pos
  have hMN : (M : ℤ) < (N : ℕ) := by
    have : (8 * M : ℤ) < (N : ℕ) := by exact_mod_cast hM
    omega
  have hv : (((labelOf N k).val : ℕ) : ℤ) = k % (N : ℕ) := by
    unfold labelOf
    simp only
    rw [Int.toNat_of_nonneg (Int.emod_nonneg k hN.ne')]
  rw [labelDistToOne_eq]
  rcases le_or_gt 0 k with h0 | h0
  · have hmod : k % (N : ℕ) = k := Int.emod_eq_of_lt h0 (by omega)
    omega
  · have hmod : k % (N : ℕ) = k + (N : ℕ) := by
      have h1 : (k + (N : ℕ) * 1) % (N : ℕ) = k % (N : ℕ) := Int.add_mul_emod_self_left k _ 1
      rw [mul_one] at h1
      rw [← h1]
      exact Int.emod_eq_of_lt (by omega) (by omega)
    omega

/-- In the partial case `K^γ < N / 8`, the window is the set of residues of the consecutive
integers `-⌊K^γ⌋, …, ⌊K^γ⌋`. These are the representatives `1 - ⌊K^γ⌋, …, 1 + ⌊K^γ⌋` of the
paper, shifted by the index convention, and no two of them coincide. -/
theorem window_partial {N : ℕ+} {K γ : ℝ} (hK : 0 ≤ K ^ γ)
    (h : K ^ γ < ((N : ℕ) : ℝ) / 8) :
    window N K γ = (Icc (-(⌊K ^ γ⌋₊ : ℤ)) (⌊K ^ γ⌋₊ : ℤ)).image (labelOf N) := by
  have hN0 : ((N : ℕ) : ℝ) ≠ 0 := by exact_mod_cast N.ne_zero
  have ht : ((N : ℕ) : ℝ) * (K ^ γ / ((N : ℕ) : ℝ)) = K ^ γ := by
    field_simp
  have hw : window N K γ = windowLabels N (K ^ γ / ((N : ℕ) : ℝ)) := by
    unfold window
    rw [windowTime_of_lt h]
  have hfl : (⌊K ^ γ⌋₊ : ℝ) ≤ K ^ γ := Nat.floor_le hK
  apply Subset.antisymm
  · rw [hw]
    have := windowLabels_subset_image N (K ^ γ / ((N : ℕ) : ℝ))
    rwa [ht] at this
  · intro i hi
    obtain ⟨k, hk, rfl⟩ := mem_image.1 hi
    rw [mem_Icc] at hk
    have hM : 8 * ⌊K ^ γ⌋₊ < N := by
      have : ((8 * ⌊K ^ γ⌋₊ : ℕ) : ℝ) < ((N : ℕ) : ℝ) := by
        push_cast
        linarith
      exact_mod_cast this
    have hd := labelDistToOne_labelOf_le hM hk.1 hk.2
    have hdR : (labelDistToOne N (labelOf N k) : ℝ) ≤ (⌊K ^ γ⌋₊ : ℝ) := by
      exact_mod_cast hd
    rw [hw]
    unfold windowLabels
    rw [mem_filter, ht]
    exact ⟨mem_univ _, by linarith⟩

/-- The nearest-neighbour pairs of the window have at most `8 K^γ` elements, for `K ≥ 1` and
`γ ≥ 0`. In the partial case the window has at most `2 K^γ + 1` labels, and `2 K^γ + 1 ≤ 3 K^γ`.
In the full case there are at most `N` labels, and `N ≤ 8 K^γ` by the full-case condition. -/
theorem card_nearestPairs_window_le {N : ℕ+} {K γ : ℝ} (hK : 1 ≤ K) (hγ : 0 ≤ γ) :
    ((nearestPairs N (window N K γ)).card : ℝ) ≤ 8 * K ^ γ := by
  have hKγ : 1 ≤ K ^ γ := Real.one_le_rpow hK hγ
  have hNpos : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
  have hpairs : (nearestPairs N (window N K γ)).card ≤ (window N K γ).card :=
    card_filter_le _ _
  by_cases h : K ^ γ < ((N : ℕ) : ℝ) / 8
  · have hw : window N K γ = windowLabels N (K ^ γ / ((N : ℕ) : ℝ)) := by
      unfold window
      rw [windowTime_of_lt h]
    have ht : ((N : ℕ) : ℝ) * (K ^ γ / ((N : ℕ) : ℝ)) = K ^ γ := by
      field_simp
    have hcard := card_windowLabels_le N (K ^ γ / ((N : ℕ) : ℝ))
    rw [ht] at hcard
    have hfl : (⌊K ^ γ⌋₊ : ℝ) ≤ K ^ γ := Nat.floor_le (by linarith)
    have h1 : (nearestPairs N (window N K γ)).card ≤ 2 * ⌊K ^ γ⌋₊ + 1 := by
      refine hpairs.trans ?_
      rw [hw]
      exact hcard
    have h2 : ((nearestPairs N (window N K γ)).card : ℝ) ≤ 2 * (⌊K ^ γ⌋₊ : ℝ) + 1 := by
      exact_mod_cast h1
    linarith
  · have hw : window N K γ = univ := window_full h
    have hfull : (N : ℕ) ≤ 8 * K ^ γ := by
      have h' : ((N : ℕ) : ℝ) / 8 ≤ K ^ γ := not_lt.1 h
      linarith
    have hcard : (nearestPairs N (window N K γ)).card ≤ (N : ℕ) := by
      refine (card_filter_le _ _).trans ?_
      rw [hw]
      simp
    have hcardR : ((nearestPairs N (window N K γ)).card : ℝ) ≤ ((N : ℕ) : ℝ) := by
      exact_mod_cast hcard
    linarith

end Riesz1

end
