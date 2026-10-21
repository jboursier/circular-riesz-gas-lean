/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriGoodCutoff
public import Riesz1.ToMathlib.Packing.UnitProduct

/-!
# Deterministic comparisons on the good event

The deterministic claims on the good event in Lemma 5.2. Let `0 < s < 1`, `γ ≥ 0`, `K ≥ 1`,
and `0 ≤ ε ≤ γ (1 - s/2)`. On the good event `A_{ε,γ}` (`Riesz1.goodEvent` of
`Riesz1/Variance/APrioriGoodCutoff.lean`), for labels `i, j` of the window `I_γ`:

* (lower comparison) `K^{-ε} d(i,j) ≤ N dist(x_i, x_j)`, and (upper comparison)
  `N dist(x_i, x_j) ≤ 2 K^ε d(i,j)`, where `d` is the cyclic index distance and `dist` is the
  circle distance `Riesz1.circDist 1`.
* (packing) a microscopic interval of length one contains at most `3 K^ε` labels of `I_γ`.
* (anchored error) `|N (x_i - x_1) - (i - 1)| ≤ K^ε d_i^{s/2}`, with `d_i = d(i, 1)`.

The paper's label `i` is the index `i - 1` of `Fin N`, and the particle lift `x_i` is `X.val i`.
The selected labels are the labels of the window `I_γ`.

Lifts at integers are the cyclic lifts `cyclicLift X a`. Lemmas here are in the namespace
`Riesz1.APG`, which keeps the names of this file apart from other helpers.
-/

@[expose] public section

noncomputable section

open Finset

namespace Riesz1

namespace APG

variable {N : ℕ+}

/-! ### Labels of integers -/

/-- The label of the integer `a` has the residue `a mod N` as its value. -/
theorem labelOf_val (a : ℤ) : ((labelOf N a : ℕ) : ℤ) = a % ((N : ℕ) : ℤ) := by
  unfold labelOf
  simp only
  exact Int.toNat_of_nonneg (Int.emod_nonneg a (by exact_mod_cast N.ne_zero))

/-- Adding a multiple of `N` does not change the label. -/
theorem labelOf_add_mul (a q : ℤ) : labelOf N (a + ((N : ℕ) : ℤ) * q) = labelOf N a := by
  apply Fin.ext
  have h : ((labelOf N (a + ((N : ℕ) : ℤ) * q) : ℕ) : ℤ) = ((labelOf N a : ℕ) : ℤ) := by
    rw [labelOf_val, labelOf_val, Int.add_mul_emod_self_left]
  exact_mod_cast h

/-- An integer is its label plus a multiple of `N`. -/
theorem val_labelOf_add (a : ℤ) :
    a = ((labelOf N a : ℕ) : ℤ) + ((N : ℕ) : ℤ) * (a / ((N : ℕ) : ℤ)) := by
  rw [labelOf_val, Int.emod_def]
  ring

/-- Shifting the index of a lift by a multiple of `N` shifts the lift by the same integer. -/
theorem cyclicLift_add_N_mul (X : Configuration N) (j q : ℤ) :
    cyclicLift X (j + ((N : ℕ) : ℤ) * q) = cyclicLift X j + q := by
  induction q using Int.induction_on with
  | zero => simp
  | succ n ih =>
    rw [show j + ((N : ℕ) : ℤ) * ((n : ℤ) + 1) = (j + ((N : ℕ) : ℤ) * n) + ((N : ℕ) : ℤ) by ring,
      cyclicLift_add_N, ih]
    push_cast
    ring
  | pred n ih =>
    have h := cyclicLift_add_N X (j + ((N : ℕ) : ℤ) * (-(n : ℤ) - 1))
    rw [show j + ((N : ℕ) : ℤ) * (-(n : ℤ) - 1) + ((N : ℕ) : ℤ)
      = j + ((N : ℕ) : ℤ) * (-(n : ℤ)) by ring, ih] at h
    push_cast at h ⊢
    linarith

/-- Gaps are periodic in their index. -/
theorem gap_add_N_mul (X : Configuration N) (j q : ℤ) :
    gap X (j + ((N : ℕ) : ℤ) * q) = gap X j := by
  unfold gap
  rw [show j + ((N : ℕ) : ℤ) * q + 1 = (j + 1) + ((N : ℕ) : ℤ) * q by ring,
    cyclicLift_add_N_mul, cyclicLift_add_N_mul]
  ring

/-- A gap is the gap at its label. -/
theorem gap_labelOf (X : Configuration N) (c : ℤ) :
    gap X c = gap X ((labelOf N c : ℕ) : ℤ) := by
  have h := gap_add_N_mul X ((labelOf N c : ℕ) : ℤ) (c / ((N : ℕ) : ℤ))
  rw [← val_labelOf_add c] at h
  exact h

/-- A lift is the lift at its label, shifted by the integer `c / N`. -/
theorem cyclicLift_labelOf (X : Configuration N) (a : ℤ) :
    cyclicLift X a = cyclicLift X ((labelOf N a : ℕ) : ℤ) + ((a / ((N : ℕ) : ℤ) : ℤ) : ℝ) := by
  have h := cyclicLift_add_N_mul X ((labelOf N a : ℕ) : ℤ) (a / ((N : ℕ) : ℤ))
  rw [← val_labelOf_add a] at h
  exact h

/-- The next label after the label of `a` is the label of `a + 1`. -/
theorem nextLabel_labelOf (a : ℤ) : nextLabel N (labelOf N a) = labelOf N (a + 1) := by
  apply Fin.ext
  have hu : ((labelOf N a : ℕ) : ℤ) = a % ((N : ℕ) : ℤ) := labelOf_val a
  have h : ((nextLabel N (labelOf N a) : ℕ) : ℤ) = ((labelOf N (a + 1) : ℕ) : ℤ) := by
    rw [labelOf_val (a + 1)]
    unfold nextLabel
    push_cast
    rw [hu, Int.emod_add_emod]
  exact_mod_cast h

/-! ### Cyclic index distance -/

/-- If `ρ = r + N m` with `0 ≤ ρ < N`, then `min ρ (N - ρ) ≤ |r|`. -/
theorem min_le_abs_of_mod {N' ρ r m : ℤ} (hN : 0 < N') (hρ0 : 0 ≤ ρ) (hρ : ρ < N')
    (hr : ρ = r + N' * m) : min ρ (N' - ρ) ≤ |r| := by
  rcases lt_trichotomy m 0 with h | h | h
  · have hm : m ≤ -1 := by omega
    have h1 : N' ≤ r := by nlinarith
    rw [abs_of_nonneg (by linarith)]
    exact (min_le_left _ _).trans (by linarith)
  · subst h
    have hr' : r = ρ := by simpa using hr.symm
    rw [hr', abs_of_nonneg hρ0]
    exact min_le_left _ _
  · have hm : 1 ≤ m := by omega
    have h1 : r ≤ ρ - N' := by nlinarith
    rw [abs_of_neg (by linarith)]
    exact (min_le_right _ _).trans (by linarith)

/-- The cyclic index distance of two labels is at most `|b - a|` for any integers `a`, `b`
whose labels are these two labels. -/
theorem cyclicIndexDistance_le_abs_labelOf (a b : ℤ) :
    ((cyclicIndexDistance N (labelOf N a) (labelOf N b) : ℕ) : ℤ) ≤ |b - a| := by
  have hN : (0 : ℤ) < ((N : ℕ) : ℤ) := by exact_mod_cast N.pos
  have hp := (labelOf N a).isLt
  have hq := (labelOf N b).isLt
  have ha := val_labelOf_add (N := N) a
  have hb := val_labelOf_add (N := N) b
  unfold cyclicIndexDistance
  rcases le_total (labelOf N a : ℕ) (labelOf N b : ℕ) with h | h
  · rw [Nat.dist_eq_sub_of_le h]
    have hle : (labelOf N b : ℕ) - (labelOf N a : ℕ) ≤ (N : ℕ) := by omega
    rw [Nat.cast_min, Nat.cast_sub hle, Nat.cast_sub h]
    have hρ0 : (0 : ℤ) ≤ ((labelOf N b : ℕ) : ℤ) - ((labelOf N a : ℕ) : ℤ) := by
      have : ((labelOf N a : ℕ) : ℤ) ≤ ((labelOf N b : ℕ) : ℤ) := by exact_mod_cast h
      linarith
    have hρ : ((labelOf N b : ℕ) : ℤ) - ((labelOf N a : ℕ) : ℤ) < ((N : ℕ) : ℤ) := by
      have : ((labelOf N b : ℕ) : ℤ) < ((N : ℕ) : ℤ) := by exact_mod_cast hq
      have : (0 : ℤ) ≤ ((labelOf N a : ℕ) : ℤ) := by positivity
      linarith
    have key := min_le_abs_of_mod (N' := ((N : ℕ) : ℤ)) hN hρ0 hρ
      (r := b - a) (m := a / ((N : ℕ) : ℤ) - b / ((N : ℕ) : ℤ)) (by linarith)
    exact key
  · rw [Nat.dist_eq_sub_of_le_right h]
    have hle : (labelOf N a : ℕ) - (labelOf N b : ℕ) ≤ (N : ℕ) := by omega
    rw [Nat.cast_min, Nat.cast_sub hle, Nat.cast_sub h]
    have hρ0 : (0 : ℤ) ≤ ((labelOf N a : ℕ) : ℤ) - ((labelOf N b : ℕ) : ℤ) := by
      have : ((labelOf N b : ℕ) : ℤ) ≤ ((labelOf N a : ℕ) : ℤ) := by exact_mod_cast h
      linarith
    have hρ : ((labelOf N a : ℕ) : ℤ) - ((labelOf N b : ℕ) : ℤ) < ((N : ℕ) : ℤ) := by
      have : ((labelOf N a : ℕ) : ℤ) < ((N : ℕ) : ℤ) := by exact_mod_cast hp
      have : (0 : ℤ) ≤ ((labelOf N b : ℕ) : ℤ) := by positivity
      linarith
    have key := min_le_abs_of_mod (N' := ((N : ℕ) : ℤ)) hN hρ0 hρ
      (r := a - b) (m := b / ((N : ℕ) : ℤ) - a / ((N : ℕ) : ℤ)) (by linarith)
    rwa [abs_sub_comm] at key

/-- Every label has cyclic index distance at most `N / 2` from any other label. -/
theorem cyclicIndexDistance_le_half (i j : Fin (N : ℕ)) :
    2 * cyclicIndexDistance N i j ≤ (N : ℕ) := by
  unfold cyclicIndexDistance Nat.dist
  have := i.isLt
  have := j.isLt
  omega

/-- For labels `i, j`, some integer `k` moves `i` to `j` with `|k| = d(i, j)`. -/
theorem exists_shift_of_cyclicIndexDistance (i j : Fin (N : ℕ)) :
    ∃ k : ℤ, labelOf N (((i : ℕ) : ℤ) + k) = j ∧ k.natAbs = cyclicIndexDistance N i j := by
  have hi := i.isLt
  have hj := j.isLt
  unfold cyclicIndexDistance Nat.dist
  rcases le_total (i : ℕ) j with h | h
  · by_cases h2 : 2 * ((j : ℕ) - i) ≤ (N : ℕ)
    · refine ⟨(j : ℤ) - i, ?_, ?_⟩
      · rw [show ((i : ℕ) : ℤ) + ((j : ℤ) - i) = ((j : ℕ) : ℤ) by ring, labelOf_natCast]
      · have : ((j : ℤ) - (i : ℤ)).natAbs = (j : ℕ) - i := by omega
        rw [this]
        omega
    · refine ⟨((j : ℤ) - i) - ((N : ℕ) : ℤ), ?_, ?_⟩
      · rw [show ((i : ℕ) : ℤ) + (((j : ℤ) - i) - ((N : ℕ) : ℤ))
          = ((j : ℕ) : ℤ) + ((N : ℕ) : ℤ) * (-1) by ring, labelOf_add_mul, labelOf_natCast]
      · have : (((j : ℤ) - i) - ((N : ℕ) : ℤ)).natAbs = (N : ℕ) - ((j : ℕ) - i) := by omega
        rw [this]
        omega
  · by_cases h2 : 2 * ((i : ℕ) - j) ≤ (N : ℕ)
    · refine ⟨(j : ℤ) - i, ?_, ?_⟩
      · rw [show ((i : ℕ) : ℤ) + ((j : ℤ) - i) = ((j : ℕ) : ℤ) by ring, labelOf_natCast]
      · have : ((j : ℤ) - (i : ℤ)).natAbs = (i : ℕ) - j := by omega
        rw [this]
        omega
    · refine ⟨((j : ℤ) - i) + ((N : ℕ) : ℤ), ?_, ?_⟩
      · rw [show ((i : ℕ) : ℤ) + (((j : ℤ) - i) + ((N : ℕ) : ℤ))
          = ((j : ℕ) : ℤ) + ((N : ℕ) : ℤ) * 1 by ring, labelOf_add_mul, labelOf_natCast]
      · have : (((j : ℤ) - i) + ((N : ℕ) : ℤ)).natAbs = (N : ℕ) - ((i : ℕ) - j) := by omega
        rw [this]
        omega

/-- The labels at cyclic distance at most `m` from a fixed label are at most `2 m + 1`. -/
theorem card_cyclic_ball_le (i0 : Fin (N : ℕ)) (m : ℕ) :
    (univ.filter fun i : Fin (N : ℕ) => cyclicIndexDistance N i0 i ≤ m).card ≤ 2 * m + 1 := by
  have hsub : (univ.filter fun i : Fin (N : ℕ) => cyclicIndexDistance N i0 i ≤ m) ⊆
      (Icc (-(m : ℤ)) (m : ℤ)).image (fun a : ℤ => labelOf N (((i0 : ℕ) : ℤ) + a)) := by
    intro i hi
    rw [mem_filter] at hi
    obtain ⟨k, hk, hkd⟩ := exists_shift_of_cyclicIndexDistance i0 i
    rw [mem_image]
    refine ⟨k, ?_, hk⟩
    rw [mem_Icc]
    have hkm : (k.natAbs : ℤ) ≤ m := by
      rw [hkd]
      exact_mod_cast hi.2
    have habs : |k| ≤ (m : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hkm
    exact abs_le.1 habs
  calc (univ.filter fun i : Fin (N : ℕ) => cyclicIndexDistance N i0 i ≤ m).card
      ≤ ((Icc (-(m : ℤ)) (m : ℤ)).image (fun a : ℤ => labelOf N (((i0 : ℕ) : ℤ) + a))).card :=
        card_le_card hsub
    _ ≤ (Icc (-(m : ℤ)) (m : ℤ)).card := card_image_le
    _ = 2 * m + 1 := by rw [Int.card_Icc]; omega

/-! ### Circle distance and gaps -/

/-- The circle distance between two labels is the circle distance between any integer lifts of
them. -/
theorem circDist_labels (X : Configuration N) (i j : Fin (N : ℕ)) {a b : ℤ}
    (ha : labelOf N a = i) (hb : labelOf N b = j) :
    circDist 1 (X.val j - X.val i) = circDist 1 (cyclicLift X b - cyclicLift X a) := by
  have hj : X.val j = cyclicLift X b - ((b / ((N : ℕ) : ℤ) : ℤ) : ℝ) := by
    have h1 := cyclicLift_labelOf X b
    rw [hb, cyclicLift_natCast] at h1
    linarith
  have hi : X.val i = cyclicLift X a - ((a / ((N : ℕ) : ℤ) : ℤ) : ℝ) := by
    have h1 := cyclicLift_labelOf X a
    rw [ha, cyclicLift_natCast] at h1
    linarith
  have key : X.val j - X.val i
      = (cyclicLift X b - cyclicLift X a) + (((a / ((N : ℕ) : ℤ) - b / ((N : ℕ) : ℤ) : ℤ) : ℝ))
          * 1 := by
    rw [hj, hi]
    push_cast
    ring
  rw [key, circDist_add_int_mul one_pos]

/-- The lifts at `N`-periodic gap indices: a sum of gap lower bounds bounds the span of lifts. -/
theorem lower_of_gaps (X : Configuration N) {a b : ℤ} (hab : a ≤ b) {g : ℝ}
    (hg : ∀ c : ℤ, a ≤ c → c < b → g ≤ gap X c) :
    g * ((b - a : ℤ) : ℝ) ≤ ((N : ℕ) : ℝ) * (cyclicLift X b - cyclicLift X a) := by
  obtain ⟨L, hL⟩ : ∃ L : ℕ, (L : ℤ) = b - a := ⟨(b - a).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hab' : a + (L : ℤ) = b := by omega
  have hbl : blockLength X a L = ((N : ℕ) : ℝ) * (cyclicLift X b - cyclicLift X a) := by
    unfold blockLength
    rw [hab']
  have hgl : g * ((b - a : ℤ) : ℝ) = (L : ℝ) * g := by
    rw [← hL]
    push_cast
    ring
  rw [hgl, ← hbl, blockLength_eq_sum]
  calc (L : ℝ) * g = ∑ _r ∈ range L, g := by simp [mul_comm]
    _ ≤ ∑ r ∈ range L, gap X (a + (r : ℤ)) := by
      apply sum_le_sum
      intro r hr
      rw [mem_range] at hr
      apply hg
      · omega
      · omega

/-- The absolute form of `lower_of_gaps`. -/
theorem mul_abs_le_of_gaps (X : Configuration N) {a b : ℤ} {g : ℝ}
    (hgap : ∀ c : ℤ, min a b ≤ c → c < max a b → g ≤ gap X c) :
    g * |((b - a : ℤ) : ℝ)| ≤ ((N : ℕ) : ℝ) * |cyclicLift X b - cyclicLift X a| := by
  have hN : (0 : ℝ) ≤ ((N : ℕ) : ℝ) := by positivity
  rcases le_total a b with h | h
  · have h1 := lower_of_gaps X h (g := g) (fun c h1 h2 =>
      hgap c (by rw [min_eq_left h]; exact h1) (by rw [max_eq_right h]; exact h2))
    have hpos : (0 : ℝ) ≤ ((b - a : ℤ) : ℝ) := by
      have : (0 : ℤ) ≤ b - a := by omega
      exact_mod_cast this
    rw [abs_of_nonneg hpos]
    exact h1.trans (mul_le_mul_of_nonneg_left (le_abs_self _) hN)
  · have h1 := lower_of_gaps X h (g := g) (fun c h1 h2 =>
      hgap c (by rw [min_eq_right h]; exact h1) (by rw [max_eq_left h]; exact h2))
    have hpos : (0 : ℝ) ≤ ((a - b : ℤ) : ℝ) := by
      have : (0 : ℤ) ≤ a - b := by omega
      exact_mod_cast this
    have hneg : ((b - a : ℤ) : ℝ) = -((a - b : ℤ) : ℝ) := by push_cast; ring
    rw [hneg, abs_neg, abs_of_nonneg hpos, abs_sub_comm (cyclicLift X b) (cyclicLift X a)]
    exact h1.trans (mul_le_mul_of_nonneg_left (le_abs_self _) hN)

/-- The gaps at two labels of the window: the nearest-neighbour bounds of the good event apply
to `gap X c` whenever `c` and `c + 1` have labels in the window. -/
theorem gap_bounds_of_labels {s K γ ε : ℝ} {X : Configuration N}
    (hX : X ∈ goodEvent N s K γ ε) {c : ℤ} (hc : labelOf N c ∈ window N K γ)
    (hc1 : labelOf N (c + 1) ∈ window N K γ) :
    K ^ (-ε) ≤ gap X c ∧ gap X c ≤ K ^ ε := by
  have hmem : labelOf N c ∈ nearestPairs N (window N K γ) :=
    mem_filter.2 ⟨hc, by rw [nextLabel_labelOf]; exact hc1⟩
  obtain ⟨h1, h2⟩ := hX.2 _ hmem
  rw [gap_labelOf X c]
  exact ⟨h1, h2⟩

/-! ### The lower and upper comparisons -/

/-- The circle distance of `y` is the distance from `y` to its nearest integer. -/
theorem circDist_one_eq_abs_sub_round (y : ℝ) : circDist 1 y = |y - ((round y : ℤ) : ℝ)| := by
  unfold circDist
  simp

/-- **Lower comparison from gap bounds, arbitrary lifts.** If every gap is at least `g ≥ 0`, then
`g d(labelOf a, labelOf b) ≤ N dist(lift b, lift a)` for all integers `a, b`. -/
theorem lower_of_gaps_labels (X : Configuration N) {g : ℝ} (hg0 : 0 ≤ g)
    (hgap : ∀ c : ℤ, g ≤ gap X c) (a b : ℤ) :
    g * ((cyclicIndexDistance N (labelOf N a) (labelOf N b) : ℕ) : ℝ) ≤
      ((N : ℕ) : ℝ) * circDist 1 (cyclicLift X b - cyclicLift X a) := by
  obtain ⟨m, hm⟩ : ∃ m : ℤ, m = round (cyclicLift X b - cyclicLift X a) := ⟨_, rfl⟩
  obtain ⟨b', hb'⟩ : ∃ b' : ℤ, b' = b + ((N : ℕ) : ℤ) * (-m) := ⟨_, rfl⟩
  have hlab : labelOf N b' = labelOf N b := by rw [hb', labelOf_add_mul]
  have hlift : cyclicLift X b' = cyclicLift X b - (m : ℝ) := by
    rw [hb', cyclicLift_add_N_mul]
    push_cast
    ring
  have hcd : circDist 1 (cyclicLift X b - cyclicLift X a)
      = |cyclicLift X b' - cyclicLift X a| := by
    rw [circDist_one_eq_abs_sub_round, ← hm, hlift]
    congr 1
    ring
  have hd : ((cyclicIndexDistance N (labelOf N a) (labelOf N b) : ℕ) : ℝ)
      ≤ |((b' - a : ℤ) : ℝ)| := by
    have h := cyclicIndexDistance_le_abs_labelOf (N := N) a b'
    rw [hlab] at h
    have h' : (((cyclicIndexDistance N (labelOf N a) (labelOf N b) : ℕ) : ℤ) : ℝ)
        ≤ ((|b' - a| : ℤ) : ℝ) := Int.cast_le.2 h
    rw [Int.cast_abs] at h'
    exact_mod_cast h'
  rw [hcd]
  calc g * ((cyclicIndexDistance N (labelOf N a) (labelOf N b) : ℕ) : ℝ)
      ≤ g * |((b' - a : ℤ) : ℝ)| := mul_le_mul_of_nonneg_left hd hg0
    _ ≤ ((N : ℕ) : ℝ) * |cyclicLift X b' - cyclicLift X a| :=
      mul_abs_le_of_gaps X (fun c _ _ => hgap c)

/-- **Lower comparison, full window.** Every gap is at least `K^{-ε}` when the window is the
whole circle, so `K^{-ε} d(i, j) ≤ N dist(x_i, x_j)` for all labels. -/
theorem lower_full_window (X : Configuration N) {g : ℝ} (hg0 : 0 ≤ g)
    (hgap : ∀ c : ℤ, g ≤ gap X c) (i j : Fin (N : ℕ)) :
    g * (cyclicIndexDistance N i j : ℝ) ≤ ((N : ℕ) : ℝ) * circDist 1 (X.val j - X.val i) := by
  obtain ⟨k, hk, -⟩ := exists_shift_of_cyclicIndexDistance i j
  have hlab_a : labelOf N ((i : ℕ) : ℤ) = i := labelOf_natCast N i
  have h := lower_of_gaps_labels X hg0 hgap ((i : ℕ) : ℤ) (((i : ℕ) : ℤ) + k)
  rw [hlab_a, hk] at h
  rw [circDist_labels X i j hlab_a hk]
  exact h

/-- The real inequality behind the partial-window span: `K^ε (2M)^{s/2} ≤ 2 K^γ` when
`0 ≤ M ≤ K^γ`. -/
theorem tolerance_le_two_mul {s K γ ε M : ℝ} (hs : 0 < s) (hs1 : s < 1) (hK : 1 ≤ K)
    (hεγ : ε ≤ γ * (1 - s / 2)) (hM0 : 0 ≤ M) (hMK : M ≤ K ^ γ) :
    K ^ ε * (2 * M) ^ (s / 2) ≤ 2 * K ^ γ := by
  have hK0 : 0 < K := by linarith
  have h2M : 2 * M ≤ 2 * K ^ γ := by linarith
  have h1 : (2 * M) ^ (s / 2) ≤ (2 * K ^ γ) ^ (s / 2) :=
    Real.rpow_le_rpow (by linarith) h2M (by linarith)
  have h2 : (2 * K ^ γ) ^ (s / 2) = 2 ^ (s / 2) * K ^ (γ * (s / 2)) := by
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hK0.le γ), Real.rpow_mul hK0.le]
  have h3 : (2 : ℝ) ^ (s / 2) ≤ 2 := by
    calc (2 : ℝ) ^ (s / 2) ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one 2
  have h4 : K ^ ε * K ^ (γ * (s / 2)) ≤ K ^ γ := by
    rw [← Real.rpow_add hK0]
    apply Real.rpow_le_rpow_of_exponent_le hK
    have : γ * (1 - s / 2) = γ - γ * (s / 2) := by ring
    linarith
  calc K ^ ε * (2 * M) ^ (s / 2) ≤ K ^ ε * (2 ^ (s / 2) * K ^ (γ * (s / 2))) := by
        rw [← h2]
        exact mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hK0.le _)
    _ = 2 ^ (s / 2) * (K ^ ε * K ^ (γ * (s / 2))) := by ring
    _ ≤ 2 * K ^ γ := mul_le_mul h3 h4 (by positivity) (by norm_num)

/-- **Span of the partial window.** On the good event, in a partial window (`K^γ < N/8`), the
lifts at the two ends `-M` and `M` of the window (`M = ⌊K^γ⌋`) lie within `N/2` in the
microscopic scale: `N (x_M - x_{-M}) < N/2`. -/
theorem partial_span_lt (X : Configuration N) {s K γ ε : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (hK : 1 ≤ K) (hγ : 0 ≤ γ) (hεγ : ε ≤ γ * (1 - s / 2))
    (hX : X ∈ goodEvent N s K γ ε) (hpart : K ^ γ < ((N : ℕ) : ℝ) / 8) (M : ℕ)
    (hM : M = ⌊K ^ γ⌋₊) :
    ((N : ℕ) : ℝ) * (cyclicLift X (M : ℤ) - cyclicLift X (-(M : ℤ))) < ((N : ℕ) : ℝ) / 2 := by
  have hK0 : 0 ≤ K ^ γ := Real.rpow_nonneg (by linarith) γ
  have hMK : (M : ℝ) ≤ K ^ γ := by
    rw [hM]
    exact Nat.floor_le hK0
  have hM1 : 1 ≤ M := by
    rw [hM]
    apply Nat.le_floor
    simpa using Real.one_le_rpow hK hγ
  have hM8 : 8 * M < (N : ℕ) := by
    have : ((8 * M : ℕ) : ℝ) < ((N : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this
  obtain ⟨q, hq⟩ : ∃ q : ℤ, ((labelOf N (-(M : ℤ)) : ℕ) : ℤ) = -(M : ℤ) + ((N : ℕ) : ℤ) * q :=
    ⟨-(-(M : ℤ) / ((N : ℕ) : ℤ)), by
      have h := val_labelOf_add (N := N) (-(M : ℤ))
      linear_combination (-1 : ℤ) * h⟩
  have hmemM : labelOf N (M : ℤ) ∈ window N K γ := by
    rw [window_partial hK0 hpart, ← hM]
    exact mem_image_of_mem _ (mem_Icc.2 ⟨by omega, le_refl _⟩)
  have hmemc : labelOf N (-(M : ℤ)) ∈ window N K γ := by
    rw [window_partial hK0 hpart, ← hM]
    exact mem_image_of_mem _ (mem_Icc.2 ⟨le_refl _, by omega⟩)
  have hsum : ((labelOf N (-(M : ℤ)) : ℕ) : ℤ) + 2 * (M : ℤ)
      = (M : ℤ) + ((N : ℕ) : ℤ) * q := by
    rw [hq]
    ring
  have hpair : (labelOf N (-(M : ℤ)), 2 * (M : ℤ)) ∈ cutoffPairs N (window N K γ) := by
    refine mem_filter.2 ⟨mem_product.2 ⟨mem_univ _,
      mem_erase.2 ⟨by omega, mem_Icc.2 ⟨by omega, by omega⟩⟩⟩, hmemc, ?_⟩
    show labelOf N (((labelOf N (-(M : ℤ)) : ℕ) : ℤ) + 2 * (M : ℤ)) ∈ window N K γ
    rw [hsum, labelOf_add_mul]
    exact hmemM
  have hb := hX.1 _ hpair
  have hnat : (2 * (M : ℤ)).natAbs = 2 * M := by omega
  unfold pairDev pairScale at hb
  dsimp only at hb
  rw [hnat] at hb
  have hshift : cyclicLift X (((labelOf N (-(M : ℤ)) : ℕ) : ℤ) + 2 * (M : ℤ))
      - cyclicLift X ((labelOf N (-(M : ℤ)) : ℕ) : ℤ)
      = cyclicLift X (M : ℤ) - cyclicLift X (-(M : ℤ)) := by
    rw [hsum, hq, cyclicLift_add_N_mul, cyclicLift_add_N_mul]
    ring
  rw [hshift] at hb
  have hbd := (abs_le.1 hb).2
  have hT := tolerance_le_two_mul hs hs1 hK hεγ (M := (M : ℝ)) (by positivity) hMK
  push_cast at hbd
  linarith

/-- **Lower comparison on the partial window.** In a partial window (`K^γ < N/8`), the labels
lie in `[-M, M]` (with `M = ⌊K^γ⌋`), and their lifts lie within `1/2`, so the circle distance
is the absolute difference of the lifts. -/
theorem lower_partial_window (X : Configuration N) {s K γ ε : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (hK : 1 ≤ K) (hγ : 0 ≤ γ) (hεγ : ε ≤ γ * (1 - s / 2))
    (hX : X ∈ goodEvent N s K γ ε) (hpart : K ^ γ < ((N : ℕ) : ℝ) / 8)
    {i j : Fin (N : ℕ)} (hi : i ∈ window N K γ) (hj : j ∈ window N K γ) :
    K ^ (-ε) * (cyclicIndexDistance N i j : ℝ) ≤ ((N : ℕ) : ℝ) * circDist 1 (X.val j - X.val i) := by
  have hK0 : 0 ≤ K ^ γ := Real.rpow_nonneg (by linarith) γ
  have hg0 : (0 : ℝ) ≤ K ^ (-ε) := Real.rpow_nonneg (by linarith) _
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = ⌊K ^ γ⌋₊ := ⟨_, rfl⟩
  have hW : window N K γ = (Icc (-(M : ℤ)) (M : ℤ)).image (labelOf N) := by
    rw [window_partial hK0 hpart, ← hM]
  have hspan := partial_span_lt X hs hs1 hK hγ hεγ hX hpart M hM
  have hNpos : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
  rw [hW] at hi hj
  obtain ⟨a, ha, rfl⟩ := mem_image.1 hi
  obtain ⟨b, hb, rfl⟩ := mem_image.1 hj
  rw [mem_Icc] at ha hb
  have hgap : ∀ c : ℤ, min a b ≤ c → c < max a b → K ^ (-ε) ≤ gap X c := by
    intro c h1 h2
    have hc : labelOf N c ∈ window N K γ := by
      rw [hW]
      exact mem_image_of_mem _ (mem_Icc.2 ⟨by omega, by omega⟩)
    have hc1 : labelOf N (c + 1) ∈ window N K γ := by
      rw [hW]
      exact mem_image_of_mem _ (mem_Icc.2 ⟨by omega, by omega⟩)
    exact (gap_bounds_of_labels hX hc hc1).1
  -- The lifts of the window lie in an interval of length `< 1/2`.
  have hmono := (cyclicLift_strictMono X).monotone
  have hD : cyclicLift X (M : ℤ) - cyclicLift X (-(M : ℤ)) < 1 / 2 := by
    by_contra hc
    push Not at hc
    nlinarith
  have hy : |cyclicLift X b - cyclicLift X a| ≤ 1 / 2 := by
    have h1 := hmono (show -(M : ℤ) ≤ a by omega)
    have h2 := hmono (show a ≤ (M : ℤ) by omega)
    have h3 := hmono (show -(M : ℤ) ≤ b by omega)
    have h4 := hmono (show b ≤ (M : ℤ) by omega)
    rw [abs_sub_le_iff]
    constructor <;> linarith
  have hyabs : circDist 1 (cyclicLift X b - cyclicLift X a) = |cyclicLift X b - cyclicLift X a| :=
    circDist_eq_abs one_pos hy
  have hd : ((cyclicIndexDistance N (labelOf N a) (labelOf N b) : ℕ) : ℝ)
      ≤ |((b - a : ℤ) : ℝ)| := by
    have h := cyclicIndexDistance_le_abs_labelOf (N := N) a b
    have h' : (((cyclicIndexDistance N (labelOf N a) (labelOf N b) : ℕ) : ℤ) : ℝ)
        ≤ ((|b - a| : ℤ) : ℝ) := Int.cast_le.2 h
    rw [Int.cast_abs] at h'
    exact_mod_cast h'
  rw [circDist_labels X (labelOf N a) (labelOf N b) rfl rfl, hyabs]
  calc K ^ (-ε) * ((cyclicIndexDistance N (labelOf N a) (labelOf N b) : ℕ) : ℝ)
      ≤ K ^ (-ε) * |((b - a : ℤ) : ℝ)| := mul_le_mul_of_nonneg_left hd hg0
    _ ≤ ((N : ℕ) : ℝ) * |cyclicLift X b - cyclicLift X a| :=
      mul_abs_le_of_gaps X hgap

/-- **Lower comparison on the good event.** For labels `i, j` of the window, `K^{-ε} d(i,j) ≤
N dist(x_i, x_j)`, where `dist` is the circle distance. -/
theorem lower_comparison (X : Configuration N) {s K γ ε : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (hK : 1 ≤ K) (hγ : 0 ≤ γ) (hεγ : ε ≤ γ * (1 - s / 2))
    (hX : X ∈ goodEvent N s K γ ε) {i j : Fin (N : ℕ)} (hi : i ∈ window N K γ)
    (hj : j ∈ window N K γ) :
    K ^ (-ε) * (cyclicIndexDistance N i j : ℝ) ≤ ((N : ℕ) : ℝ) * circDist 1 (X.val j - X.val i) := by
  have hg0 : (0 : ℝ) ≤ K ^ (-ε) := Real.rpow_nonneg (by linarith) _
  by_cases hpart : K ^ γ < ((N : ℕ) : ℝ) / 8
  · exact lower_partial_window X hs hs1 hK hγ hεγ hX hpart hi hj
  · have hW : window N K γ = univ := window_full hpart
    refine lower_full_window X hg0 (fun c => ?_) i j
    have hc : labelOf N c ∈ window N K γ := by
      rw [hW]
      exact mem_univ _
    have hc1 : labelOf N (c + 1) ∈ window N K γ := by
      rw [hW]
      exact mem_univ _
    exact (gap_bounds_of_labels hX hc hc1).1

/-- **Upper comparison on the good event.** For labels `i, j` of the window,
`N dist(x_i, x_j) ≤ 2 K^ε d(i,j)`. -/
theorem upper_comparison (X : Configuration N) {s K γ ε : ℝ} (hs1 : s < 1) (hK : 1 ≤ K)
    (hε : 0 ≤ ε) (hX : X ∈ goodEvent N s K γ ε) {i j : Fin (N : ℕ)} (hi : i ∈ window N K γ)
    (hj : j ∈ window N K γ) :
    ((N : ℕ) : ℝ) * circDist 1 (X.val j - X.val i)
      ≤ 2 * K ^ ε * (cyclicIndexDistance N i j : ℝ) := by
  by_cases hij : i = j
  · subst hij
    have h0 : ((cyclicIndexDistance N i i : ℕ) : ℝ) = 0 := by
      unfold cyclicIndexDistance
      simp
    have hε0 : (0 : ℝ) ≤ K ^ ε := Real.rpow_nonneg (by linarith) ε
    simp [circDist, h0]
  obtain ⟨k, hk, hkd⟩ := exists_shift_of_cyclicIndexDistance i j
  have hlab_a : labelOf N ((i : ℕ) : ℤ) = i := labelOf_natCast N i
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hij
    have h1 : labelOf N ((i : ℕ) : ℤ) = j := by simpa using hk
    rw [hlab_a] at h1
    exact h1
  have hdpos : (1 : ℝ) ≤ (cyclicIndexDistance N i j : ℝ) := by
    have : 1 ≤ cyclicIndexDistance N i j := by
      rw [← hkd]
      exact Int.natAbs_pos.2 hk0
    exact_mod_cast this
  have hdhalf := cyclicIndexDistance_le_half i j
  have hmem : (i, k) ∈ cutoffPairs N (window N K γ) := by
    refine mem_filter.2 ⟨mem_product.2 ⟨mem_univ _, mem_erase.2 ⟨hk0, mem_Icc.2 ⟨?_, ?_⟩⟩⟩,
      hi, ?_⟩
    · have : k.natAbs ≤ (N : ℕ) / 2 := by omega
      omega
    · have : k.natAbs ≤ (N : ℕ) / 2 := by omega
      omega
    · show labelOf N (((i : ℕ) : ℤ) + k) ∈ window N K γ
      rw [hk]
      exact hj
  have hb := hX.1 _ hmem
  unfold pairDev pairScale at hb
  dsimp only at hb
  rw [hkd] at hb
  have hkR : |(k : ℝ)| = ((cyclicIndexDistance N i j : ℕ) : ℝ) := by
    have h1 := Int.abs_eq_natAbs k
    have h2 : ((|k| : ℤ) : ℝ) = ((((cyclicIndexDistance N i j : ℕ)) : ℤ) : ℝ) := by
      rw [h1, ← hkd]
    rw [Int.cast_abs] at h2
    simpa using h2
  have hpow : ((cyclicIndexDistance N i j : ℕ) : ℝ) ^ (s / 2)
      ≤ ((cyclicIndexDistance N i j : ℕ) : ℝ) := by
    calc ((cyclicIndexDistance N i j : ℕ) : ℝ) ^ (s / 2)
        ≤ ((cyclicIndexDistance N i j : ℕ) : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hdpos (by linarith)
      _ = ((cyclicIndexDistance N i j : ℕ) : ℝ) := Real.rpow_one _
  have hK1 : (1 : ℝ) ≤ K ^ ε := Real.one_le_rpow hK hε
  have hdK : ((cyclicIndexDistance N i j : ℕ) : ℝ) ≤ K ^ ε * ((cyclicIndexDistance N i j : ℕ) : ℝ) := by
    nlinarith
  have hΔ : |((N : ℕ) : ℝ) * (cyclicLift X (((i : ℕ) : ℤ) + k) - cyclicLift X ((i : ℕ) : ℤ))|
      ≤ 2 * K ^ ε * ((cyclicIndexDistance N i j : ℕ) : ℝ) := by
    have htri := abs_add_le (((N : ℕ) : ℝ) * (cyclicLift X (((i : ℕ) : ℤ) + k)
      - cyclicLift X ((i : ℕ) : ℤ)) - (k : ℝ)) (k : ℝ)
    rw [sub_add_cancel] at htri
    have hmul := mul_le_mul_of_nonneg_left hpow (by linarith : (0 : ℝ) ≤ K ^ ε)
    nlinarith
  rw [circDist_labels X i j hlab_a hk]
  have hc := circDist_le_abs_sub one_pos
    (cyclicLift X (((i : ℕ) : ℤ) + k) - cyclicLift X ((i : ℕ) : ℤ)) 0
  simp only [Int.cast_zero, mul_zero, sub_zero] at hc
  have hN0 : (0 : ℝ) ≤ ((N : ℕ) : ℝ) := by positivity
  calc ((N : ℕ) : ℝ) * circDist 1 (cyclicLift X (((i : ℕ) : ℤ) + k)
        - cyclicLift X ((i : ℕ) : ℤ))
      ≤ ((N : ℕ) : ℝ) * |cyclicLift X (((i : ℕ) : ℤ) + k)
          - cyclicLift X ((i : ℕ) : ℤ)| := mul_le_mul_of_nonneg_left hc hN0
    _ = |((N : ℕ) : ℝ) * (cyclicLift X (((i : ℕ) : ℤ) + k)
          - cyclicLift X ((i : ℕ) : ℤ))| := by
        rw [abs_mul, abs_of_nonneg hN0]
    _ ≤ 2 * K ^ ε * ((cyclicIndexDistance N i j : ℕ) : ℝ) := hΔ

/-! ### Packing and the anchored error -/

/-- **Packing.** On the good event, a microscopic interval `[t₀, t₀ + 1/N)`, taken modulo one,
contains at most `3 K^ε` particles with labels in the window. -/
theorem packing_window (X : Configuration N) {s K γ ε : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (hK : 1 ≤ K) (hγ : 0 ≤ γ) (hε : 0 ≤ ε) (hεγ : ε ≤ γ * (1 - s / 2))
    (hX : X ∈ goodEvent N s K γ ε) (t₀ : ℝ) :
    ((({i : Fin (N : ℕ) | i ∈ window N K γ ∧
      ∃ q : ℤ, X.val i + q ∈ Set.Ico t₀ (t₀ + 1 / ((N : ℕ) : ℝ))}).ncard : ℕ) : ℝ)
      ≤ 3 * K ^ ε := by
  have hNpos : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
  have hK0 : (0 : ℝ) < K := by linarith
  have hKε0 : (0 : ℝ) < K ^ ε := Real.rpow_pos_of_pos hK0 ε
  have hKε1 : (1 : ℝ) ≤ K ^ ε := Real.one_le_rpow hK hε
  obtain ⟨S, hS⟩ : ∃ S : Set (Fin (N : ℕ)), S = {i : Fin (N : ℕ) | i ∈ window N K γ ∧
      ∃ q : ℤ, X.val i + q ∈ Set.Ico t₀ (t₀ + 1 / ((N : ℕ) : ℝ))} := ⟨_, rfl⟩
  rw [← hS]
  rcases S.eq_empty_or_nonempty with hempty | ⟨i0, hi0⟩
  · rw [hempty, Set.ncard_empty]
    simp only [Nat.cast_zero]
    positivity
  · rw [hS] at hi0
    obtain ⟨hi0w, q0, hq0⟩ := hi0
    have hsub : S ⊆ ↑((univ : Finset (Fin (N : ℕ))).filter
        fun i => cyclicIndexDistance N i0 i ≤ ⌊K ^ ε⌋₊) := by
      intro i hi
      rw [hS] at hi
      obtain ⟨hiw, q, hq⟩ := hi
      rw [Finset.mem_coe, mem_filter]
      refine ⟨mem_univ _, ?_⟩
      obtain ⟨hq1, hq2⟩ := Set.mem_Ico.1 hq
      obtain ⟨hq3, hq4⟩ := Set.mem_Ico.1 hq0
      have hcirc : circDist 1 (X.val i - X.val i0) < 1 / ((N : ℕ) : ℝ) := by
        have h := circDist_le_abs_sub one_pos (X.val i - X.val i0) (q0 - q)
        simp only [Int.cast_sub, one_mul] at h
        refine lt_of_le_of_lt h ?_
        rw [abs_lt]
        constructor <;> linarith
      have hlow := lower_comparison X hs hs1 hK hγ hεγ hX hi0w hiw
      have hN1 : ((N : ℕ) : ℝ) * circDist 1 (X.val i - X.val i0) < 1 := by
        calc ((N : ℕ) : ℝ) * circDist 1 (X.val i - X.val i0)
            < ((N : ℕ) : ℝ) * (1 / ((N : ℕ) : ℝ)) := mul_lt_mul_of_pos_left hcirc hNpos
          _ = 1 := mul_one_div_cancel hNpos.ne'
      have hlt : K ^ (-ε) * (cyclicIndexDistance N i0 i : ℝ) < 1 := lt_of_le_of_lt hlow hN1
      have hdlt : (cyclicIndexDistance N i0 i : ℝ) < K ^ ε := by
        rw [Real.rpow_neg (by linarith)] at hlt
        have := (inv_mul_lt_iff₀ hKε0).1 hlt
        linarith
      exact Nat.le_floor hdlt.le
    have hcard : S.ncard ≤ ((univ : Finset (Fin (N : ℕ))).filter
        fun i => cyclicIndexDistance N i0 i ≤ ⌊K ^ ε⌋₊).card := by
      rw [← Set.ncard_coe_finset]
      exact Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    have hball := card_cyclic_ball_le (N := N) i0 ⌊K ^ ε⌋₊
    have hfl : (⌊K ^ ε⌋₊ : ℝ) ≤ K ^ ε := Nat.floor_le hKε0.le
    have hcardR : (S.ncard : ℝ) ≤ 2 * (⌊K ^ ε⌋₊ : ℝ) + 1 := by
      have : S.ncard ≤ 2 * ⌊K ^ ε⌋₊ + 1 := hcard.trans hball
      exact_mod_cast this
    linarith

/-- **Anchored error.** On the good event, for a label `i` of the window, the anchored coordinate
`N (x_i - x_1)` differs from `i - 1` (here the index `(i : ℕ)`) by at most `K^ε d(i,1)^{s/2}`. -/
theorem anchored_error (X : Configuration N) {s K γ ε : ℝ} (hK : 1 ≤ K)
    (hX : X ∈ goodEvent N s K γ ε) {i : Fin (N : ℕ)}
    (hi : i ∈ window N K γ) :
    |((N : ℕ) : ℝ) * (X.val i - X.val ⟨0, N.pos⟩) - ((i : ℕ) : ℝ)|
      ≤ K ^ ε * ((labelDistToOne N i : ℕ) : ℝ) ^ (s / 2) := by
  have hK0 : (0 : ℝ) ≤ K := by linarith
  have hwt : 0 ≤ windowTime N K γ := by
    unfold windowTime
    split_ifs <;> positivity
  have hzw : (⟨0, N.pos⟩ : Fin (N : ℕ)) ∈ window N K γ := by
    unfold window windowLabels
    rw [mem_filter]
    refine ⟨mem_univ _, ?_⟩
    have h0 : labelDistToOne N ⟨0, N.pos⟩ = 0 := by
      rw [labelDistToOne_eq]
      simp
    rw [h0]
    simp only [Nat.cast_zero]
    exact mul_nonneg (Nat.cast_nonneg _) hwt
  by_cases h0 : (i : ℕ) = 0
  · have hiz : i = ⟨0, N.pos⟩ := Fin.ext h0
    subst hiz
    simp
    exact mul_nonneg (Real.rpow_nonneg hK0 _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · have hi0 : 1 ≤ (i : ℕ) := Nat.one_le_iff_ne_zero.2 h0
    have hiN := i.isLt
    by_cases hhalf : 2 * (i : ℕ) ≤ (N : ℕ)
    · have hmem : ((⟨0, N.pos⟩ : Fin (N : ℕ)), ((i : ℕ) : ℤ)) ∈ cutoffPairs N (window N K γ) := by
        refine mem_filter.2 ⟨mem_product.2 ⟨mem_univ _,
          mem_erase.2 ⟨by omega, mem_Icc.2 ⟨by omega, by omega⟩⟩⟩, hzw, ?_⟩
        show labelOf N (((0 : ℕ) : ℤ) + ((i : ℕ) : ℤ)) ∈ window N K γ
        rw [Nat.cast_zero, zero_add, labelOf_natCast]
        exact hi
      have hb := hX.1 _ hmem
      unfold pairDev pairScale at hb
      dsimp only at hb
      have e1 : cyclicLift X ((((⟨0, N.pos⟩ : Fin (N : ℕ)) : ℕ) : ℤ) + ((i : ℕ) : ℤ))
          = X.val i := by
        rw [show ((⟨0, N.pos⟩ : Fin (N : ℕ)) : ℕ) = 0 from rfl, Nat.cast_zero, zero_add,
          cyclicLift_natCast]
      have e2 : cyclicLift X ((0 : ℕ) : ℤ) = X.val ⟨0, N.pos⟩ := cyclicLift_natCast X ⟨0, N.pos⟩
      rw [e1, e2] at hb
      have hnat : (((i : ℕ) : ℤ)).natAbs = (i : ℕ) := by omega
      rw [hnat] at hb
      have hd : labelDistToOne N i = (i : ℕ) := by
        rw [labelDistToOne_eq]
        omega
      rw [hd]
      push_cast at hb
      exact hb
    · have hmem : ((⟨0, N.pos⟩ : Fin (N : ℕ)), ((i : ℕ) : ℤ) - ((N : ℕ) : ℤ))
          ∈ cutoffPairs N (window N K γ) := by
        refine mem_filter.2 ⟨mem_product.2 ⟨mem_univ _,
          mem_erase.2 ⟨by omega, mem_Icc.2 ⟨by omega, by omega⟩⟩⟩, hzw, ?_⟩
        show labelOf N (((0 : ℕ) : ℤ) + (((i : ℕ) : ℤ) - ((N : ℕ) : ℤ))) ∈ window N K γ
        rw [show ((0 : ℕ) : ℤ) + (((i : ℕ) : ℤ) - ((N : ℕ) : ℤ))
          = ((i : ℕ) : ℤ) + ((N : ℕ) : ℤ) * (-1) by ring, labelOf_add_mul, labelOf_natCast]
        exact hi
      have hb := hX.1 _ hmem
      unfold pairDev pairScale at hb
      dsimp only at hb
      have e1 : (((⟨0, N.pos⟩ : Fin (N : ℕ)) : ℕ) : ℤ) + (((i : ℕ) : ℤ) - ((N : ℕ) : ℤ))
          = ((i : ℕ) : ℤ) + ((N : ℕ) : ℤ) * (-1) := by
        rw [show ((⟨0, N.pos⟩ : Fin (N : ℕ)) : ℕ) = 0 from rfl, Nat.cast_zero]
        ring
      have e2 : cyclicLift X ((0 : ℕ) : ℤ) = X.val ⟨0, N.pos⟩ := cyclicLift_natCast X ⟨0, N.pos⟩
      rw [e1, cyclicLift_add_N_mul, cyclicLift_natCast, e2] at hb
      have hnat : (((i : ℕ) : ℤ) - ((N : ℕ) : ℤ)).natAbs = (N : ℕ) - (i : ℕ) := by omega
      rw [hnat] at hb
      have hd : labelDistToOne N i = (N : ℕ) - (i : ℕ) := by
        rw [labelDistToOne_eq]
        omega
      rw [hd, Nat.cast_sub (by omega)]
      push_cast at hb
      have hring : ((N : ℕ) : ℝ) * (X.val i + -1 - X.val ⟨0, N.pos⟩)
          - (((i : ℕ) : ℝ) - ((N : ℕ) : ℝ)) = ((N : ℕ) : ℝ) * (X.val i - X.val ⟨0, N.pos⟩)
          - ((i : ℕ) : ℝ) := by ring
      rw [hring, Nat.cast_sub (show (i : ℕ) ≤ (N : ℕ) by omega)] at hb
      exact hb

end APG

/-- **Deterministic claims on the good event in Lemma 5.2.**
Let `0 < s < 1` and `0 < γ`, and put `ε₀ = γ (1 - s/2) > 0`. For every `0 < ε ≤ ε₀`, every
`N`, every real `K ≥ 1`, and every configuration `X` of the good event `A_{ε,γ}`:

* for all labels `i, j` of the window `I_γ`, the lower and upper comparisons
  `K^{-ε} d(i,j) ≤ N dist(x_i, x_j) ≤ 2 K^ε d(i,j)` hold, with `dist` the circle distance
  `circDist 1` and `d` the cyclic index distance.
* every microscopic interval `[t₀, t₀ + 1/N)`, taken modulo one, contains at most `3 K^ε`
  particles with labels in the window.
* for every label `i` of the window, `|N (x_i - x_1) - (i - 1)| ≤ K^ε d(i, 1)^{s/2}`, written with
  the index `(i : ℕ)` of `Fin N` (so the paper's `i - 1` is `(i : ℕ)`). -/
theorem aPrioriGood_deterministic {s γ : ℝ} (hs : 0 < s) (hs1 : s < 1) (hγ : 0 < γ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ (N : ℕ+) (K : ℝ), 1 ≤ K →
      ∀ X : Configuration N, X ∈ goodEvent N s K γ ε →
        (∀ i j : Fin (N : ℕ), i ∈ window N K γ → j ∈ window N K γ →
          K ^ (-ε) * (cyclicIndexDistance N i j : ℝ)
              ≤ ((N : ℕ) : ℝ) * circDist 1 (X.val j - X.val i) ∧
            ((N : ℕ) : ℝ) * circDist 1 (X.val j - X.val i)
              ≤ 2 * K ^ ε * (cyclicIndexDistance N i j : ℝ)) ∧
        (∀ t₀ : ℝ, ((({i : Fin (N : ℕ) | i ∈ window N K γ ∧
            ∃ q : ℤ, X.val i + q ∈ Set.Ico t₀ (t₀ + 1 / ((N : ℕ) : ℝ))}).ncard : ℕ) : ℝ)
              ≤ 3 * K ^ ε) ∧
        (∀ i : Fin (N : ℕ), i ∈ window N K γ →
          |((N : ℕ) : ℝ) * (X.val i - X.val ⟨0, N.pos⟩) - ((i : ℕ) : ℝ)|
            ≤ K ^ ε * ((labelDistToOne N i : ℕ) : ℝ) ^ (s / 2)) := by
  refine ⟨γ * (1 - s / 2), mul_pos hγ (by linarith), fun ε hε hεγ N K hK X hX => ?_⟩
  refine ⟨fun i j hi hj => ⟨?_, ?_⟩, fun t₀ => ?_, fun i hi => ?_⟩
  · exact APG.lower_comparison X hs hs1 hK hγ.le hεγ hX hi hj
  · exact APG.upper_comparison X hs1 hK hε.le hX hi hj
  · exact APG.packing_window X hs hs1 hK hγ.le hε.le hεγ hX t₀
  · exact APG.anchored_error X hK hX hi

end Riesz1

end
end
