/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriGoodCutoff

/-!
# Pairs of the good-event cutoff as block deviations

Support lemmas for the probability estimate in Lemma 5.2 (the file
`Riesz1/Variance/APrioriGoodProbability.lean` assembles them). The main results are:

* `APrioriProb.blockLength_eq_labelOf`: a block length depends only on the label of its start,
  so the rigidity conclusion, which is stated for labels, applies to every integer start.
* `APrioriProb.abs_pairDev_eq`: for a pair `p = (i, k)` with `k ≠ 0`, the deviation
  `|pairDev N X p|` equals `|blockLength X j |k| - |k||`, where `j = i` if `k > 0` and `j = i + k`
  if `k < 0`.
* `APrioriProb.natAbs_le_of_mem_cutoffPairs`: for `K ≥ 1`, every pair of the window has
  `|k| ≤ 4 K^γ`. This is item 1 of the paper's proof.
* `APrioriProb.card_cutoffPairs_le`: the number of pairs is at most `72 K^{2γ}`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Finset

namespace Riesz1

namespace APrioriProb

variable {N : ℕ+}

/-! ### Residues and periodicity -/

/-- The label of an integer is its residue modulo `N`. -/
theorem labelOf_cast (N : ℕ+) (a : ℤ) :
    ((labelOf N a : ℕ) : ℤ) = a % ((N : ℕ) : ℤ) := by
  unfold labelOf
  exact Int.toNat_of_nonneg (Int.emod_nonneg a (by exact_mod_cast N.ne_zero))

/-- Every integer is its label plus a multiple of `N`. -/
theorem eq_labelOf_add_N_mul_div (N : ℕ+) (j : ℤ) :
    j = ((labelOf N j : ℕ) : ℤ) + ((N : ℕ) : ℤ) * (j / ((N : ℕ) : ℤ)) := by
  rw [labelOf_cast, Int.emod_def]
  ring

/-- The cyclic lift moves by `q` when the index moves by `N q`. -/
theorem cyclicLift_add_N_mul (X : Configuration N) (x : ℤ) (q : ℤ) :
    cyclicLift X (x + ((N : ℕ) : ℤ) * q) = cyclicLift X x + q := by
  refine Int.induction_on q ?_ (fun i ih => ?_) (fun i ih => ?_)
  · simp
  · rw [show x + ((N : ℕ) : ℤ) * ((i : ℤ) + 1) = (x + ((N : ℕ) : ℤ) * i) + ((N : ℕ) : ℤ) by ring,
      cyclicLift_add_N, ih]
    push_cast
    ring
  · have h1 := cyclicLift_add_N X (x + ((N : ℕ) : ℤ) * (-(i : ℤ) - 1))
    rw [show x + ((N : ℕ) : ℤ) * (-(i : ℤ) - 1) + ((N : ℕ) : ℤ) = x + ((N : ℕ) : ℤ) * (-(i : ℤ))
      by ring, ih] at h1
    push_cast at h1 ⊢
    linarith

/-- A block length is unchanged when the start moves by a multiple of `N`. -/
theorem blockLength_add_N_mul (X : Configuration N) (x q : ℤ) (L : ℕ) :
    blockLength X (x + ((N : ℕ) : ℤ) * q) L = blockLength X x L := by
  unfold blockLength
  rw [show x + ((N : ℕ) : ℤ) * q + (L : ℤ) = (x + (L : ℤ)) + ((N : ℕ) : ℤ) * q by ring,
    cyclicLift_add_N_mul, cyclicLift_add_N_mul]
  ring

/-- A block length starting at `j` equals the block length starting at the label of `j`. -/
theorem blockLength_eq_labelOf (X : Configuration N) (j : ℤ) (L : ℕ) :
    blockLength X j L = blockLength X ((labelOf N j : ℕ) : ℤ) L := by
  have h := blockLength_add_N_mul X ((labelOf N j : ℕ) : ℤ) (j / ((N : ℕ) : ℤ)) L
  rw [← eq_labelOf_add_N_mul_div N j] at h
  exact h

/-- A block of one gap is that gap. -/
theorem blockLength_one (X : Configuration N) (j : ℤ) : blockLength X j 1 = gap X j := by
  rw [blockLength_eq_sum]
  simp

/-! ### Deviations of a pair -/

/-- For a pair with positive second coordinate, the deviation is the block deviation at the
first label. -/
theorem abs_pairDev_of_pos (X : Configuration N) (i : Fin (N : ℕ)) (L : ℕ) :
    |pairDev N X (i, (L : ℤ))| = |blockLength X ((i : ℕ) : ℤ) L - (L : ℝ)| := by
  unfold pairDev blockLength
  simp only [Int.cast_natCast]

/-- For a pair with negative second coordinate `-L`, the deviation is minus the block deviation
of the block starting at `i - L`. -/
theorem abs_pairDev_of_neg (X : Configuration N) (i : Fin (N : ℕ)) (L : ℕ) :
    |pairDev N X (i, -(L : ℤ))| = |blockLength X (((i : ℕ) : ℤ) + -(L : ℤ)) L - (L : ℝ)| := by
  unfold pairDev blockLength
  rw [← abs_neg]
  congr 1
  rw [show ((i : ℕ) : ℤ) + -(L : ℤ) + (L : ℤ) = ((i : ℕ) : ℤ) by ring]
  push_cast
  ring

/-- The absolute pair deviation is the absolute block deviation of the block that starts at
`i` when `k > 0` and at `i + k` when `k < 0`, with length `|k|`. -/
theorem abs_pairDev_eq (X : Configuration N) (i : Fin (N : ℕ)) (k : ℤ) (hk : k ≠ 0) :
    |pairDev N X (i, k)| =
      |blockLength X (((i : ℕ) : ℤ) + min k 0) (k.natAbs) - ((k.natAbs : ℕ) : ℝ)| := by
  obtain ⟨L, hL | hL⟩ := Int.eq_nat_or_neg k
  · subst hL
    have hLpos : L ≠ 0 := fun h0 => hk (by rw [h0]; rfl)
    have hmin : min (L : ℤ) 0 = 0 := min_eq_right (Nat.cast_nonneg L)
    rw [hmin, Int.natAbs_natCast, add_zero]
    exact abs_pairDev_of_pos X i L
  · subst hL
    have hmin : min (-(L : ℤ)) 0 = -(L : ℤ) := min_eq_left (neg_nonpos.2 (Nat.cast_nonneg L))
    rw [hmin, Int.natAbs_neg, Int.natAbs_natCast]
    exact abs_pairDev_of_neg X i L

/-! ### Pairs of the window -/

/-- Membership in the set of cutoff pairs, unpacked. -/
theorem mem_cutoffPairs_iff (I : Finset (Fin (N : ℕ))) (p : Fin (N : ℕ) × ℤ) :
    p ∈ cutoffPairs N I ↔ p.1 ∈ I ∧ labelOf N (((p.1 : ℕ) : ℤ) + p.2) ∈ I ∧
      p.2 ≠ 0 ∧ -(((N : ℕ) / 2 : ℕ) : ℤ) ≤ p.2 ∧ p.2 ≤ (((N : ℕ) / 2 : ℕ) : ℤ) := by
  unfold cutoffPairs
  simp only [mem_filter, mem_product, mem_erase, mem_Icc, mem_univ, true_and]
  constructor
  · rintro ⟨⟨h0, h1, h2⟩, h3, h4⟩
    exact ⟨h3, h4, h0, h1, h2⟩
  · rintro ⟨h3, h4, h0, h1, h2⟩
    exact ⟨⟨h0, h1, h2⟩, h3, h4⟩

/-- **Length of a pair of the window.** For `K ≥ 1` and `γ ≥ 0`, every cutoff pair `p` has
`|p.2| ≤ 4 K^γ`. In the full window `N ≤ 8 K^γ`. In the partial window both labels lie in the
window of radius `⌊K^γ⌋`, and their difference is the only integer of that size congruent to
`p.2` modulo `N`. -/
theorem natAbs_le_of_mem_cutoffPairs (K γ : ℝ) (hK : 1 ≤ K) (hγ : 0 ≤ γ) {p : Fin (N : ℕ) × ℤ}
    (hp : p ∈ cutoffPairs N (window N K γ)) :
    ((p.2.natAbs : ℕ) : ℝ) ≤ 4 * K ^ γ := by
  rw [mem_cutoffPairs_iff] at hp
  obtain ⟨hi, hik, -, hk1, hk2⟩ := hp
  have hKγ : 1 ≤ K ^ γ := Real.one_le_rpow hK hγ
  have hNpos : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
  by_cases h : K ^ γ < ((N : ℕ) : ℝ) / 8
  · -- Partial window: both labels are residues of integers of size at most `M`.
    set M : ℕ := ⌊K ^ γ⌋₊ with hM
    have hMK : (M : ℝ) ≤ K ^ γ := Nat.floor_le (by linarith)
    have h8 : (8 * M : ℝ) < ((N : ℕ) : ℝ) := by linarith
    have h8' : 8 * (M : ℤ) < ((N : ℕ) : ℤ) := by
      have : ((8 * M : ℕ) : ℝ) < ((N : ℕ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    rw [window_partial (by linarith) h, mem_image] at hi hik
    obtain ⟨a, ha, hai⟩ := hi
    obtain ⟨b, hb, hbk⟩ := hik
    rw [mem_Icc] at ha hb
    -- Congruences: `i ≡ a` and `i + k ≡ b` modulo `N`.
    have hia : ((((p.1 : ℕ)) : ℤ)) = a % ((N : ℕ) : ℤ) := by
      rw [← labelOf_cast, hai]
    have hbk' : b % ((N : ℕ) : ℤ) = (((p.1 : ℕ) : ℤ) + p.2) % ((N : ℕ) : ℤ) := by
      rw [← labelOf_cast, ← labelOf_cast, hbk]
    have hd1 : ((N : ℕ) : ℤ) ∣ a - ((p.1 : ℕ) : ℤ) := by
      refine ⟨a / ((N : ℕ) : ℤ), ?_⟩
      rw [hia, Int.emod_def]
      ring
    have hd2 : ((N : ℕ) : ℤ) ∣ (((p.1 : ℕ) : ℤ) + p.2) - b := by
      refine ⟨((((p.1 : ℕ) : ℤ) + p.2) / ((N : ℕ) : ℤ)) - b / ((N : ℕ) : ℤ), ?_⟩
      rw [Int.emod_def, Int.emod_def] at hbk'
      linarith
    have hdiv : ((N : ℕ) : ℤ) ∣ p.2 - (b - a) := by
      have := dvd_add hd2 hd1
      have e : (((p.1 : ℕ) : ℤ) + p.2 - b) + (a - ((p.1 : ℕ) : ℤ)) = p.2 - (b - a) := by ring
      rwa [e] at this
    have hsmall : |p.2 - (b - a)| < ((N : ℕ) : ℤ) := by
      have hk1' : -(((N : ℕ) / 2 : ℕ) : ℤ) ≤ p.2 := hk1
      have hk2' : p.2 ≤ (((N : ℕ) / 2 : ℕ) : ℤ) := hk2
      rw [abs_lt]
      constructor <;> omega
    have hzero : p.2 - (b - a) = 0 := Int.eq_zero_of_abs_lt_dvd hdiv hsmall
    have hnat : p.2.natAbs ≤ 2 * M := by
      have : |p.2| ≤ 2 * (M : ℤ) := by
        rw [abs_le]
        constructor <;> omega
      omega
    have hnatR : ((p.2.natAbs : ℕ) : ℝ) ≤ 2 * (M : ℝ) := by exact_mod_cast hnat
    linarith
  · -- Full window: `N ≤ 8 K^γ`, and `|p.2| ≤ N / 2`.
    have hfull : ((N : ℕ) : ℝ) ≤ 8 * K ^ γ := by
      have h' : ((N : ℕ) : ℝ) / 8 ≤ K ^ γ := not_lt.1 h
      linarith
    have hnat : 2 * p.2.natAbs ≤ (N : ℕ) := by omega
    have hnatR : (2 : ℝ) * ((p.2.natAbs : ℕ) : ℝ) ≤ ((N : ℕ) : ℝ) := by exact_mod_cast hnat
    linarith

/-! ### Cardinalities -/

/-- **Size of the window.** For `K ≥ 1` and `γ ≥ 0`, the window has at most `8 K^γ` labels. In
the partial case it has at most `2 ⌊K^γ⌋ + 1 ≤ 3 K^γ` labels. In the full case it is all of
`Fin N`, and `N ≤ 8 K^γ`. -/
theorem card_window_le (K γ : ℝ) (hK : 1 ≤ K) (hγ : 0 ≤ γ) :
    ((window N K γ).card : ℝ) ≤ 8 * K ^ γ := by
  have hKγ : 1 ≤ K ^ γ := Real.one_le_rpow hK hγ
  by_cases h : K ^ γ < ((N : ℕ) : ℝ) / 8
  · set M : ℕ := ⌊K ^ γ⌋₊ with hM
    have hMK : (M : ℝ) ≤ K ^ γ := Nat.floor_le (by linarith)
    have hsub : (window N K γ).card ≤ (Icc (-(M : ℤ)) (M : ℤ)).card := by
      rw [window_partial (by linarith) h]
      exact card_image_le
    rw [Int.card_Icc] at hsub
    have hnat : (window N K γ).card ≤ 2 * M + 1 := by omega
    have hR : ((window N K γ).card : ℝ) ≤ 2 * (M : ℝ) + 1 := by exact_mod_cast hnat
    linarith
  · have hw : window N K γ = univ := window_full h
    have hfull : ((N : ℕ) : ℝ) ≤ 8 * K ^ γ := by
      have h' : ((N : ℕ) : ℝ) / 8 ≤ K ^ γ := not_lt.1 h
      linarith
    rw [hw, card_univ, Fintype.card_fin]
    linarith

/-- **Number of pairs.** For `K ≥ 1` and `γ ≥ 0`, the cutoff pairs number at most
`72 K^{2γ}`. They lie in the window times the integers of size at most `4 K^γ`. -/
theorem card_cutoffPairs_le (K γ : ℝ) (hK : 1 ≤ K) (hγ : 0 ≤ γ) :
    ((cutoffPairs N (window N K γ)).card : ℝ) ≤ 72 * K ^ (2 * γ) := by
  have hKγ : 1 ≤ K ^ γ := Real.one_le_rpow hK hγ
  set M : ℕ := ⌊4 * K ^ γ⌋₊ with hM
  have hMK : (M : ℝ) ≤ 4 * K ^ γ := Nat.floor_le (by linarith)
  have hsub : cutoffPairs N (window N K γ) ⊆ window N K γ ×ˢ Icc (-(M : ℤ)) (M : ℤ) := by
    intro p hp
    have h4 := natAbs_le_of_mem_cutoffPairs K γ hK hγ hp
    have hnat : p.2.natAbs ≤ M := Nat.le_floor h4
    rw [mem_cutoffPairs_iff] at hp
    rw [mem_product, mem_Icc]
    exact ⟨hp.1, by omega, by omega⟩
  have hcard := card_le_card hsub
  rw [card_product, Int.card_Icc] at hcard
  have hnat : (cutoffPairs N (window N K γ)).card ≤ (window N K γ).card * (2 * M + 1) := by
    have e : ((M : ℤ) + 1 - -(M : ℤ)).toNat = 2 * M + 1 := by omega
    rw [e] at hcard
    exact hcard
  have hR : ((cutoffPairs N (window N K γ)).card : ℝ) ≤
      ((window N K γ).card : ℝ) * (2 * (M : ℝ) + 1) := by
    have := (Nat.cast_le (α := ℝ)).2 hnat
    push_cast at this
    exact this
  have hW := card_window_le (N := N) K γ hK hγ
  have hM9 : 2 * (M : ℝ) + 1 ≤ 9 * K ^ γ := by linarith
  have hK2 : K ^ (2 * γ) = K ^ γ * K ^ γ := by
    rw [two_mul, Real.rpow_add (by linarith)]
  rw [hK2]
  calc ((cutoffPairs N (window N K γ)).card : ℝ)
      ≤ ((window N K γ).card : ℝ) * (2 * (M : ℝ) + 1) := hR
    _ ≤ (8 * K ^ γ) * (9 * K ^ γ) :=
        mul_le_mul hW hM9 (by positivity) (by linarith)
    _ = 72 * (K ^ γ * K ^ γ) := by ring

end APrioriProb

end Riesz1

end
end
