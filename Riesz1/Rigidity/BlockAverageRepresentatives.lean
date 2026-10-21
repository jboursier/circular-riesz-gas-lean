/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Tactic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Int.Interval

/-!
# Cyclic neighbourhoods and their integer representatives

Labels are integers, and the label `j` has residue `j mod N` in `ℤ/Nℤ`.
This file defines three objects, for `N ≥ 1`:

* `cyclicDist N i j`, the cyclic distance `d(i,j) = min(|a - b|, N - |a - b|)` of the Euclidean
  remainders `a = i mod N` and `b = j mod N` in `{0, …, N-1}`.
* `cyclicNbhd N k i`, the neighbourhood `I_k(i) = {j ∈ ℤ/Nℤ : d(i,j) ≤ k}`.
* `cyclicRep N k i`, the chosen integer representatives `J_k(i)`: the interval `{i-k, …, i+k}` when
  `2k < N`, and `{i-k+1, …, i+k}` when `2k = N`.

The definitions describe the paper's objects for `1 ≤ k ≤ ⌊N/2⌋`. The main result is
`Riesz1.cyclicRep_bijOn`: for such `k`, reduction modulo `N` maps `J_k(i)` bijectively onto
`I_k(i)`, so `J_k(i)` is a set of representatives of `I_k(i)`.
-/

@[expose] public section

open Finset

namespace Riesz1

/-! ### Definitions -/

/-- The cyclic distance `d(i,j)`. With the Euclidean remainders
`a = i mod N` and `b = j mod N` in `{0, …, N-1}`, it is `min(|a - b|, N - |a - b|)`. -/
def cyclicDist (N : ℕ+) (i j : ℤ) : ℤ :=
  min |i % ((N : ℕ) : ℤ) - j % ((N : ℕ) : ℤ)|
    (((N : ℕ) : ℤ) - |i % ((N : ℕ) : ℤ) - j % ((N : ℕ) : ℤ)|)

/-- The neighbourhood `I_k(i) = {j ∈ ℤ/Nℤ : d(i,j) ≤ k}`. A residue `j`
is measured through its representative `j.val` in `{0, …, N-1}`. -/
def cyclicNbhd (N : ℕ+) (k : ℕ) (i : ℤ) : Set (ZMod (N : ℕ)) :=
  {j | cyclicDist N i (j.val : ℤ) ≤ k}

/-- The chosen integer representatives `J_k(i)`: the interval
`{i-k, …, i+k}` when `2k < N`, and `{i-k+1, …, i+k}` when `2k = N`. -/
def cyclicRep (N : ℕ+) (k : ℕ) (i : ℤ) : Finset ℤ :=
  if 2 * k < (N : ℕ) then Finset.Icc (i - k) (i + k) else Finset.Icc (i - k + 1) (i + k)

/-! ### Membership in the representatives -/

/-- In the case `2k < N`, the representatives are the labels `i - k ≤ j ≤ i + k`. -/
theorem mem_cyclicRep_of_two_mul_lt {N : ℕ+} {k : ℕ} {i j : ℤ} (h : 2 * k < (N : ℕ)) :
    j ∈ cyclicRep N k i ↔ i - k ≤ j ∧ j ≤ i + k := by
  simp only [cyclicRep, h, ↓reduceIte, mem_Icc]

/-- In the case `2k ≥ N`, the representatives are the labels `i - k + 1 ≤ j ≤ i + k`. -/
theorem mem_cyclicRep_of_not_two_mul_lt {N : ℕ+} {k : ℕ} {i j : ℤ} (h : ¬ 2 * k < (N : ℕ)) :
    j ∈ cyclicRep N k i ↔ i - k + 1 ≤ j ∧ j ≤ i + k := by
  simp only [cyclicRep, h, ↓reduceIte, mem_Icc]

/-- The representatives are nonempty when `k ≥ 1`. -/
theorem cyclicRep_card_pos {N : ℕ+} {k : ℕ} (hk : 1 ≤ k) (i : ℤ) :
    0 < (cyclicRep N k i).card := by
  refine Finset.card_pos.2 ⟨i + k, ?_⟩
  by_cases h : 2 * k < (N : ℕ)
  · rw [mem_cyclicRep_of_two_mul_lt h]
    constructor <;> omega
  · rw [mem_cyclicRep_of_not_two_mul_lt h]
    constructor <;> omega

/-- Shifting the labels by `N` shifts the representatives by `N`. -/
theorem cyclicRep_add_N (N : ℕ+) (k : ℕ) (i : ℤ) :
    cyclicRep N k (i + ((N : ℕ) : ℤ)) = (cyclicRep N k i).map (addRightEmbedding ((N : ℕ) : ℤ)) := by
  unfold cyclicRep
  by_cases h : 2 * k < (N : ℕ)
  · simp only [h, ↓reduceIte]
    rw [map_add_right_Icc]
    congr 1 <;> ring
  · simp only [h, ↓reduceIte]
    rw [map_add_right_Icc]
    congr 1 <;> ring

/-! ### Integer inequalities -/

/-- For `n ≥ 0`, integers `δ` and `m`: the number `min(|δ|, n - |δ|)` is at most `|δ + n m|`. -/
theorem min_abs_le_abs_add_mul {n δ m : ℤ} (hn : 0 ≤ n) :
    min |δ| (n - |δ|) ≤ |δ + n * m| := by
  rcases lt_trichotomy m 0 with hm | rfl | hm
  · rcases le_total 0 δ with hδ | hδ
    · refine min_le_of_right_le (le_trans ?_ (neg_le_abs _))
      rw [abs_of_nonneg hδ]
      nlinarith [mul_nonneg hn (show (0 : ℤ) ≤ -m - 1 by omega)]
    · refine min_le_of_left_le (le_trans ?_ (neg_le_abs _))
      rw [abs_of_nonpos hδ]
      nlinarith [mul_nonneg hn (show (0 : ℤ) ≤ -m by omega)]
  · simp
  · rcases le_total 0 δ with hδ | hδ
    · refine min_le_of_left_le ?_
      rw [abs_of_nonneg hδ]
      exact le_trans (by nlinarith [mul_nonneg hn (show (0 : ℤ) ≤ m by omega)]) (le_abs_self _)
    · refine min_le_of_right_le ?_
      rw [abs_of_nonpos hδ]
      exact le_trans (by nlinarith [mul_nonneg hn (show (0 : ℤ) ≤ m - 1 by omega)]) (le_abs_self _)

/-! ### The cyclic distance -/

/-- The cyclic distance is at most the absolute difference of the labels: `d(i,j) ≤ |j - i|`. -/
theorem cyclicDist_le_abs (N : ℕ+) (i j : ℤ) : cyclicDist N i j ≤ |j - i| := by
  have key := min_abs_le_abs_add_mul (n := ((N : ℕ) : ℤ))
    (δ := i % ((N : ℕ) : ℤ) - j % ((N : ℕ) : ℤ)) (m := i / ((N : ℕ) : ℤ) - j / ((N : ℕ) : ℤ))
    (Int.natCast_nonneg _)
  have heq : i % ((N : ℕ) : ℤ) - j % ((N : ℕ) : ℤ)
      + ((N : ℕ) : ℤ) * (i / ((N : ℕ) : ℤ) - j / ((N : ℕ) : ℤ)) = i - j := by
    rw [Int.emod_def i, Int.emod_def j]
    ring
  rw [heq, abs_sub_comm i j] at key
  exact key

/-- The cyclic distance depends on a label only through its residue: replacing `j` by the
representative `(j mod N) ∈ {0, …, N-1}` does not change `d(i,j)`. -/
theorem cyclicDist_val_intCast (N : ℕ+) (i j : ℤ) :
    cyclicDist N i ((j : ZMod (N : ℕ)).val : ℤ) = cyclicDist N i j := by
  have hval : (((j : ZMod (N : ℕ)).val : ℕ) : ℤ) = j % ((N : ℕ) : ℤ) := ZMod.val_intCast j
  unfold cyclicDist
  rw [hval, Int.emod_emod]

/-! ### Representatives as intervals -/

/-- The first label of `J_k(i)`: `i - k` when `2k < N`, and `i - k + 1` when `2k = N`. -/
def cyclicRepStart (N : ℕ+) (k : ℕ) (i : ℤ) : ℤ :=
  if 2 * k < (N : ℕ) then i - k else i - k + 1

/-- The number of gaps `L` of `J_k(i)`, so that `J_k(i)` has `L + 1` labels: `L = 2k` when
`2k < N`, and `L = 2k - 1` when `2k = N`. -/
def cyclicRepSpan (N : ℕ+) (k : ℕ) : ℕ :=
  if 2 * k < (N : ℕ) then 2 * k else 2 * k - 1

/-- For `1 ≤ k`, the representatives are the `L + 1` consecutive labels from `cyclicRepStart`. -/
theorem cyclicRep_eq_Icc {N : ℕ+} {k : ℕ} (hk : 1 ≤ k) (i : ℤ) :
    cyclicRep N k i =
      Finset.Icc (cyclicRepStart N k i) (cyclicRepStart N k i + cyclicRepSpan N k) := by
  unfold cyclicRep cyclicRepStart cyclicRepSpan
  by_cases h : 2 * k < (N : ℕ)
  · simp only [h, ↓reduceIte]
    congr 1
    omega
  · simp only [h, ↓reduceIte]
    congr 1
    omega

/-! ### Reduction modulo `N` of the representatives -/

/-- Every label of `J_k(i)` lies in `I_k(i)` after reduction modulo `N`. -/
theorem cyclicRep_mapsTo {N : ℕ+} {k : ℕ} (i : ℤ) :
    Set.MapsTo (fun j : ℤ => (j : ZMod (N : ℕ))) (cyclicRep N k i : Set ℤ) (cyclicNbhd N k i) := by
  intro j hj
  have hj' : j ∈ cyclicRep N k i := hj
  show cyclicDist N i (((j : ZMod (N : ℕ))).val : ℤ) ≤ k
  rw [cyclicDist_val_intCast]
  refine (cyclicDist_le_abs N i j).trans ?_
  by_cases h : 2 * k < (N : ℕ)
  · obtain ⟨h1, h2⟩ := (mem_cyclicRep_of_two_mul_lt h).1 hj'
    exact abs_le.2 ⟨by omega, by omega⟩
  · obtain ⟨h1, h2⟩ := (mem_cyclicRep_of_not_two_mul_lt h).1 hj'
    exact abs_le.2 ⟨by omega, by omega⟩

/-- Reduction modulo `N` is injective on `J_k(i)`: two labels of `J_k(i)` with equal residues are
equal, because their difference has absolute value below `N` when `2k ≤ N`. -/
theorem cyclicRep_injOn {N : ℕ+} {k : ℕ} (hkN : 2 * k ≤ (N : ℕ)) (i : ℤ) :
    Set.InjOn (fun j : ℤ => (j : ZMod (N : ℕ))) (cyclicRep N k i : Set ℤ) := by
  intro j hj j' hj' hjj'
  have hj1 : j ∈ cyclicRep N k i := hj
  have hj2 : j' ∈ cyclicRep N k i := hj'
  have hdvd : ((N : ℕ) : ℤ) ∣ j' - j := (ZMod.intCast_eq_intCast_iff_dvd_sub j j' (N : ℕ)).1 hjj'
  have hlt : |j' - j| < ((N : ℕ) : ℤ) := by
    by_cases h : 2 * k < (N : ℕ)
    · obtain ⟨h1, h2⟩ := (mem_cyclicRep_of_two_mul_lt h).1 hj1
      obtain ⟨h3, h4⟩ := (mem_cyclicRep_of_two_mul_lt h).1 hj2
      exact abs_lt.2 ⟨by omega, by omega⟩
    · obtain ⟨h1, h2⟩ := (mem_cyclicRep_of_not_two_mul_lt h).1 hj1
      obtain ⟨h3, h4⟩ := (mem_cyclicRep_of_not_two_mul_lt h).1 hj2
      exact abs_lt.2 ⟨by omega, by omega⟩
  have := Int.eq_zero_of_abs_lt_dvd hdvd hlt
  omega

/-- Integer decomposition in the odd case: if `-n < δ < n` and `min(|δ|, n - |δ|) ≤ k`, then
`δ = r + n c` for integers `c` and `r` with `|r| ≤ k`. -/
theorem exists_small_rep_of_lt {n k δ : ℤ} (hδ : -n < δ)
    (hδ' : δ < n) (hd : min |δ| (n - |δ|) ≤ k) :
    ∃ r c : ℤ, -k ≤ r ∧ r ≤ k ∧ δ = r + n * c := by
  rcases min_le_iff.1 hd with h | h
  · exact ⟨δ, 0, (abs_le.1 h).1, (abs_le.1 h).2, by ring⟩
  · rcases le_total 0 δ with h0 | h0
    · rw [abs_of_nonneg h0] at h
      exact ⟨δ - n, 1, by omega, by omega, by ring⟩
    · rw [abs_of_nonpos h0] at h
      exact ⟨δ + n, -1, by omega, by omega, by ring⟩

/-- In the case `2k = N` every difference `δ` of remainders has a decomposition `δ = r + N c` with
`-k + 1 ≤ r ≤ k`, so the representatives meet every residue. -/
theorem exists_rep_of_eq {n k δ : ℤ} (hn : n = 2 * k) (hδ : -n < δ) (hδ' : δ < n) :
    ∃ r c : ℤ, -k + 1 ≤ r ∧ r ≤ k ∧ δ = r + n * c := by
  by_cases h1 : δ ≤ -k
  · exact ⟨δ + n, -1, by omega, by omega, by ring⟩
  · by_cases h2 : k < δ
    · exact ⟨δ - n, 1, by omega, by omega, by ring⟩
    · exact ⟨δ, 0, by omega, by omega, by ring⟩

/-- Every residue of `I_k(i)` is the reduction of a label of `J_k(i)`. -/
theorem cyclicRep_surjOn {N : ℕ+} {k : ℕ} (hkN : 2 * k ≤ (N : ℕ)) (i : ℤ) :
    Set.SurjOn (fun j : ℤ => (j : ZMod (N : ℕ))) (cyclicRep N k i : Set ℤ) (cyclicNbhd N k i) := by
  intro z hz
  have hz' : cyclicDist N i (z.val : ℤ) ≤ k := hz
  have hn : (0 : ℤ) < ((N : ℕ) : ℤ) := by exact_mod_cast N.pos
  have hb0 : (0 : ℤ) ≤ (z.val : ℤ) := Int.natCast_nonneg _
  have hb1 : (z.val : ℤ) < ((N : ℕ) : ℤ) := by exact_mod_cast ZMod.val_lt z
  have ha0 : (0 : ℤ) ≤ i % ((N : ℕ) : ℤ) := Int.emod_nonneg _ hn.ne'
  have ha1 : i % ((N : ℕ) : ℤ) < ((N : ℕ) : ℤ) := Int.emod_lt_of_pos _ hn
  have hi : i = i % ((N : ℕ) : ℤ) + ((N : ℕ) : ℤ) * (i / ((N : ℕ) : ℤ)) := by
    rw [Int.emod_def i]
    ring
  have hzN : ((z.val : ℤ) : ZMod (N : ℕ)) = z := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  -- The distance of the remainders, written with the difference `δ = b - a`.
  have hd : min |(z.val : ℤ) - i % ((N : ℕ) : ℤ)|
      (((N : ℕ) : ℤ) - |(z.val : ℤ) - i % ((N : ℕ) : ℤ)|) ≤ k := by
    unfold cyclicDist at hz'
    rw [Int.emod_eq_of_lt hb0 hb1, abs_sub_comm (i % ((N : ℕ) : ℤ)) (z.val : ℤ)] at hz'
    exact hz'
  have hδ : -((N : ℕ) : ℤ) < (z.val : ℤ) - i % ((N : ℕ) : ℤ) := by linarith
  have hδ' : (z.val : ℤ) - i % ((N : ℕ) : ℤ) < ((N : ℕ) : ℤ) := by linarith
  by_cases h : 2 * k < (N : ℕ)
  · obtain ⟨r, c, hr1, hr2, hrc⟩ :=
      exists_small_rep_of_lt hδ hδ' hd
    refine ⟨i + r, (mem_cyclicRep_of_two_mul_lt h).2 ⟨by omega, by omega⟩, ?_⟩
    show ((i + r : ℤ) : ZMod (N : ℕ)) = z
    rw [← hzN, ZMod.intCast_eq_intCast_iff_dvd_sub]
    exact ⟨c - i / ((N : ℕ) : ℤ), by linear_combination hrc - hi⟩
  · have hN : ((N : ℕ) : ℤ) = 2 * (k : ℤ) := by
      have : (N : ℕ) = 2 * k := by omega
      exact_mod_cast this
    obtain ⟨r, c, hr1, hr2, hrc⟩ := exists_rep_of_eq hN hδ hδ'
    refine ⟨i + r, (mem_cyclicRep_of_not_two_mul_lt h).2 ⟨by omega, by omega⟩, ?_⟩
    show ((i + r : ℤ) : ZMod (N : ℕ)) = z
    rw [← hzN, ZMod.intCast_eq_intCast_iff_dvd_sub]
    exact ⟨c - i / ((N : ℕ) : ℤ), by linear_combination hrc - hi⟩

/-- Reduction modulo `N` is a bijection from the representatives `J_k(i)` onto the neighbourhood
`I_k(i)`, for `2k ≤ N`. The range `1 ≤ k ≤ ⌊N/2⌋` is a special case. -/
theorem cyclicRep_bijOn {N : ℕ+} {k : ℕ} (hkN : 2 * k ≤ (N : ℕ)) (i : ℤ) :
    Set.BijOn (fun j : ℤ => (j : ZMod (N : ℕ))) (cyclicRep N k i : Set ℤ) (cyclicNbhd N k i) :=
  ⟨cyclicRep_mapsTo i, cyclicRep_injOn hkN i, cyclicRep_surjOn hkN i⟩

end Riesz1

end
