/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingConvolutionEvent

/-!
# Arcs and separations under the good event

The cutoff part of Lemma 5.8. On the good event `𝒜_{ε,γ'}` of
`gradEvent s γ' ε N ℓ X`, the nearest-neighbour gaps are bounded below and above, and the lifted
separations `x_{i+k} - x_i` are bounded below by the arc length times `K^{-ε}/N`.

Two window facts are used throughout:

* In a full window, the labels are `{0, …, N-1}`, but the gaps and the pair bounds hold for every
  integer label, because the lifts satisfy `x_{j+N} = x_j + 1` (`gradLift_add_mul`).
* In a partial window, the labels form an interval, so the gaps between two labels of the window
  are gaps of labels of the window.

The `K^{-ε}` and `K^ε` below are written `((N : ℝ) * ℓ) ^ (-ε)` and `((N : ℝ) * ℓ) ^ ε`.
-/

@[expose] public section

open Finset

namespace Riesz1

noncomputable section

/-- A label between two labels of a partial window lies in the window. -/
lemma mem_gradLabels_of_between_partial {ℓ γ : ℝ} {N : ℕ+} (hP : GradPartial N ℓ γ) {i j m : ℤ}
    (hi : i ∈ gradLabels N ℓ γ) (hj : j ∈ gradLabels N ℓ γ) (h1 : i ≤ m) (h2 : m ≤ j) :
    m ∈ gradLabels N ℓ γ := by
  rw [mem_gradLabels_partial hP] at hi hj ⊢
  omega

/-- The edge bounds `K^{-ε} ≤ N (x_{l+1} - x_l) ≤ K^ε` hold at every integer label `l` of a full
window, because the gap is `N`-periodic in `l`. -/
lemma gradEvent_edge_of_full {s γ ε ℓ : ℝ} {N : ℕ+} {X : Fin (N : ℕ) → ℝ}
    (hev : gradEvent s γ ε N ℓ X) (hfull : ¬GradPartial N ℓ γ) (l : ℤ) :
    ((N : ℝ) * ℓ) ^ (-ε) ≤ (N : ℝ) * (gradLift N X (l + 1) - gradLift N X l) ∧
      (N : ℝ) * (gradLift N X (l + 1) - gradLift N X l) ≤ ((N : ℝ) * ℓ) ^ ε := by
  have hNpos : (0 : ℤ) < (N : ℤ) := by exact_mod_cast N.pos
  obtain ⟨q, r0, h0, hlt, rfl⟩ : ∃ q r0 : ℤ, 0 ≤ r0 ∧ r0 < (N : ℤ) ∧
      l = r0 + (N : ℤ) * q :=
    ⟨l / (N : ℤ), l % (N : ℤ), Int.emod_nonneg _ hNpos.ne', Int.emod_lt_of_pos _ hNpos,
      (by linarith [Int.emod_add_mul_ediv l (N : ℤ)])⟩
  have hmem : r0 ∈ gradLabels N ℓ γ := (mem_gradLabels_full hfull r0).2 ⟨h0, hlt⟩
  have hwin : gradInWindow N ℓ γ (r0 + 1) := fun hP => absurd hP hfull
  obtain ⟨h1, h2⟩ := hev.2 r0 hmem hwin
  have hshift1 : gradLift N X (r0 + (N : ℤ) * q + 1) = gradLift N X (r0 + 1) + q := by
    rw [show r0 + (N : ℤ) * q + 1 = (r0 + 1) + (N : ℤ) * q by ring, gradLift_add_mul]
  have hshift0 : gradLift N X (r0 + (N : ℤ) * q) = gradLift N X r0 + q :=
    gradLift_add_mul N X r0 q
  rw [hshift1, hshift0,
    show gradLift N X (r0 + 1) + q - (gradLift N X r0 + q) =
      gradLift N X (r0 + 1) - gradLift N X r0 by ring]
  exact ⟨h1, h2⟩

/-- The edge bounds at a label `l`, when either the window is full or both `l` and `l + 1` are
labels of the window. -/
lemma gradEvent_edge_bounds {s γ ε ℓ : ℝ} {N : ℕ+} {X : Fin (N : ℕ) → ℝ}
    (hev : gradEvent s γ ε N ℓ X) (l : ℤ)
    (hl : ¬GradPartial N ℓ γ ∨ (l ∈ gradLabels N ℓ γ ∧ l + 1 ∈ gradLabels N ℓ γ)) :
    ((N : ℝ) * ℓ) ^ (-ε) ≤ (N : ℝ) * (gradLift N X (l + 1) - gradLift N X l) ∧
      (N : ℝ) * (gradLift N X (l + 1) - gradLift N X l) ≤ ((N : ℝ) * ℓ) ^ ε := by
  rcases hl with hfull | ⟨hm, hm1⟩
  · exact gradEvent_edge_of_full hev hfull l
  · exact hev.2 l hm (fun _ => hm1)

/-- Arc bounds: for `n` consecutive gaps starting at the label `i`, the scaled length
`N (x_{i+n} - x_i)` lies between `K^{-ε} n` and `K^ε n`, provided every gap of the arc is an edge
of the window. -/
lemma gradEvent_arc_bounds {s γ ε ℓ : ℝ} {N : ℕ+} {X : Fin (N : ℕ) → ℝ}
    (hev : gradEvent s γ ε N ℓ X) (i : ℤ) (n : ℕ)
    (hedge : ∀ m : ℤ, i ≤ m → m < i + n →
      ¬GradPartial N ℓ γ ∨ (m ∈ gradLabels N ℓ γ ∧ m + 1 ∈ gradLabels N ℓ γ)) :
    ((N : ℝ) * ℓ) ^ (-ε) * n ≤ (N : ℝ) * (gradLift N X (i + n) - gradLift N X i) ∧
      (N : ℝ) * (gradLift N X (i + n) - gradLift N X i) ≤ ((N : ℝ) * ℓ) ^ ε * n := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun m h1 h2 => hedge m h1 (by push_cast; omega))
    obtain ⟨e1, e2⟩ := gradEvent_edge_bounds hev (i + n)
      (hedge (i + n) (by omega) (by push_cast; omega))
    have hidx : i + ((n + 1 : ℕ) : ℤ) = i + n + 1 := by push_cast; ring
    have hsplit : (N : ℝ) * (gradLift N X (i + n + 1) - gradLift N X i) =
        (N : ℝ) * (gradLift N X (i + n) - gradLift N X i) +
          (N : ℝ) * (gradLift N X (i + n + 1) - gradLift N X (i + n)) := by ring
    have hc : ((N : ℝ) * ℓ) ^ (-ε) * ((n + 1 : ℕ) : ℝ) =
        ((N : ℝ) * ℓ) ^ (-ε) * n + ((N : ℝ) * ℓ) ^ (-ε) := by push_cast; ring
    have hd : ((N : ℝ) * ℓ) ^ ε * ((n + 1 : ℕ) : ℝ) =
        ((N : ℝ) * ℓ) ^ ε * n + ((N : ℝ) * ℓ) ^ ε := by push_cast; ring
    rw [hidx]
    constructor
    · rw [hc, hsplit]
      linarith
    · rw [hd, hsplit]
      linarith

/-- The good event gives the first clause of `gradEvent` at every integer label `i` and every
integer `k` with `2|k| ≤ N`, once the endpoints lie in the window. The window is full, so the
pair bound is `N`-periodic in `i`. -/
lemma gradEvent_pair_bound {s γ ε ℓ : ℝ} {N : ℕ+} {X : Fin (N : ℕ) → ℝ}
    (hev : gradEvent s γ ε N ℓ X) (hℓ : 0 < ℓ) (i k : ℤ) (hk : 2 * |k| ≤ (N : ℤ))
    (hi : ¬GradPartial N ℓ γ ∨ (i ∈ gradLabels N ℓ γ ∧ i + k ∈ gradLabels N ℓ γ)) :
    |(N : ℝ) * (gradLift N X (i + k) - gradLift N X i) - k| ≤
      ((N : ℝ) * ℓ) ^ ε * |(k : ℝ)| ^ (s / 2) := by
  by_cases hk0 : k = 0
  · subst hk0
    have hK : 0 ≤ ((N : ℝ) * ℓ) ^ ε := Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg _) hℓ.le) _
    have h0 : 0 ≤ |((0 : ℤ) : ℝ)| ^ (s / 2) := Real.rpow_nonneg (abs_nonneg _) _
    have := mul_nonneg hK h0
    simpa using this
  · by_cases hP : GradPartial N ℓ γ
    · rcases hi with h | ⟨hm, hw⟩
      · exact absurd hP h
      · exact hev.1 i hm k (fun _ => hw) hk0 hk
    · have hNpos : (0 : ℤ) < (N : ℤ) := by exact_mod_cast N.pos
      obtain ⟨q, i0, h0, hlt, rfl⟩ : ∃ q i0 : ℤ, 0 ≤ i0 ∧ i0 < (N : ℤ) ∧
          i = i0 + (N : ℤ) * q :=
        ⟨i / (N : ℤ), i % (N : ℤ), Int.emod_nonneg _ hNpos.ne', Int.emod_lt_of_pos _ hNpos,
          (by linarith [Int.emod_add_mul_ediv i (N : ℤ)])⟩
      have hmem : i0 ∈ gradLabels N ℓ γ := (mem_gradLabels_full hP i0).2 ⟨h0, hlt⟩
      have hwin : gradInWindow N ℓ γ (i0 + k) := fun h => absurd h hP
      have hev' := hev.1 i0 hmem k hwin hk0 hk
      have hshift1 : gradLift N X (i0 + (N : ℤ) * q + k) = gradLift N X (i0 + k) + q := by
        rw [show i0 + (N : ℤ) * q + k = (i0 + k) + (N : ℤ) * q by ring, gradLift_add_mul]
      have hshift0 : gradLift N X (i0 + (N : ℤ) * q) = gradLift N X i0 + q :=
        gradLift_add_mul N X i0 q
      rw [hshift1, hshift0,
        show gradLift N X (i0 + k) + q - (gradLift N X i0 + q) =
          gradLift N X (i0 + k) - gradLift N X i0 by ring]
      exact hev'

/-- The scaled separation of a pair of labels `i` and `i + k` is at least `K^{-ε} |k|`. The
hypothesis `hi` says that the endpoints lie in the window, or that the window is full. -/
lemma gradEvent_sep_lower {s γ ε ℓ : ℝ} {N : ℕ+} {X : Fin (N : ℕ) → ℝ}
    (hev : gradEvent s γ ε N ℓ X) (i k : ℤ)
    (hi : ¬GradPartial N ℓ γ ∨ (i ∈ gradLabels N ℓ γ ∧ i + k ∈ gradLabels N ℓ γ)) :
    ((N : ℝ) * ℓ) ^ (-ε) * |(k : ℝ)| ≤
      |(N : ℝ) * (gradLift N X (i + k) - gradLift N X i)| := by
  rcases le_total 0 k with hk | hk
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    have hedge : ∀ m : ℤ, i ≤ m → m < i + (n : ℤ) →
        ¬GradPartial N ℓ γ ∨ (m ∈ gradLabels N ℓ γ ∧ m + 1 ∈ gradLabels N ℓ γ) := by
      intro m h1 h2
      rcases hi with hP | ⟨hi0, hin⟩
      · exact Or.inl hP
      · by_cases hP : GradPartial N ℓ γ
        · exact Or.inr ⟨mem_gradLabels_of_between_partial hP hi0 hin h1 (by omega),
            mem_gradLabels_of_between_partial hP hi0 hin (by omega) (by omega)⟩
        · exact Or.inl hP
    obtain ⟨h1, -⟩ := gradEvent_arc_bounds hev i n hedge
    have habs : |((n : ℤ) : ℝ)| = (n : ℝ) := by
      rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n)]
    rw [habs]
    exact le_trans h1 (le_abs_self _)
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.mpr hk)
    have hsum : i + k + (n : ℤ) = i := by omega
    have hedge : ∀ m : ℤ, i + k ≤ m → m < i + k + (n : ℤ) →
        ¬GradPartial N ℓ γ ∨ (m ∈ gradLabels N ℓ γ ∧ m + 1 ∈ gradLabels N ℓ γ) := by
      intro m h1 h2
      rcases hi with hP | ⟨hi0, hin⟩
      · exact Or.inl hP
      · by_cases hP : GradPartial N ℓ γ
        · exact Or.inr ⟨mem_gradLabels_of_between_partial hP hin hi0 h1 (by omega),
            mem_gradLabels_of_between_partial hP hin hi0 (by omega) (by omega)⟩
        · exact Or.inl hP
    obtain ⟨h1, -⟩ := gradEvent_arc_bounds hev (i + k) n hedge
    rw [hsum] at h1
    have hkR : |(k : ℝ)| = (n : ℝ) := by
      have hk' : (k : ℝ) = -(n : ℝ) := by
        have hk'' : k = -(n : ℤ) := by omega
        rw [hk'']
        push_cast
        ring
      rw [hk', abs_neg, abs_of_nonneg (Nat.cast_nonneg n)]
    rw [hkR]
    have e : (N : ℝ) * (gradLift N X (i + k) - gradLift N X i) =
        -((N : ℝ) * (gradLift N X i - gradLift N X (i + k))) := by ring
    rw [e, abs_neg]
    exact le_trans h1 (le_abs_self _)

/-- In a full window, the scaled complementary arc: `K^{-ε} (N - |k|) ≤ N (1 - |x_{i+k} - x_i|)`
for `|k| ≤ N`. The arc from `i + k` (or from `i`) to `i + N` (or to `i + k + N`) has `N - |k|`
gaps, and `x_{j+N} = x_j + 1`. -/
lemma gradEvent_sep_complement {s γ ε ℓ : ℝ} {N : ℕ+} {X : Fin (N : ℕ) → ℝ}
    (hev : gradEvent s γ ε N ℓ X) (hℓ : 0 < ℓ) (hfull : ¬GradPartial N ℓ γ) (i k : ℤ)
    (hk : |k| ≤ (N : ℤ)) :
    ((N : ℝ) * ℓ) ^ (-ε) * ((N : ℝ) - |(k : ℝ)|) ≤
      (N : ℝ) * (1 - |gradLift N X (i + k) - gradLift N X i|) := by
  have hK0 : 0 ≤ ((N : ℝ) * ℓ) ^ (-ε) :=
    Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg _) hℓ.le) _
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast N.pos
  have hper : ∀ j : ℤ, gradLift N X (j + (N : ℤ)) = gradLift N X j + 1 := by
    intro j
    simpa using gradLift_add_mul N X j 1
  rcases le_total 0 k with hk0 | hk0
  · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hk0
    have hp : (p : ℤ) ≤ (N : ℤ) := by
      have := le_abs_self ((p : ℤ))
      linarith
    obtain ⟨q, hq⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ (N : ℤ) - (p : ℤ))
    have harc1 := gradEvent_arc_bounds hev i p (fun _ _ _ => Or.inl hfull)
    have harc2 := gradEvent_arc_bounds hev (i + p) q (fun _ _ _ => Or.inl hfull)
    have hend : i + p + (q : ℤ) = i + (N : ℤ) := by omega
    rw [hend, hper i] at harc2
    have hqR : (N : ℝ) - (p : ℝ) = (q : ℝ) := by
      have : (N : ℤ) - (p : ℤ) = (q : ℤ) := by omega
      exact_mod_cast this
    have hnn : 0 ≤ (N : ℝ) * (gradLift N X (i + p) - gradLift N X i) :=
      le_trans (mul_nonneg hK0 (Nat.cast_nonneg p)) harc1.1
    have hr : |gradLift N X (i + p) - gradLift N X i| =
        gradLift N X (i + p) - gradLift N X i :=
      abs_of_nonneg (nonneg_of_mul_nonneg_right (by linarith [hnn]) hNpos)
    have hpabs : |((p : ℤ) : ℝ)| = (p : ℝ) := by
      rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg p)]
    rw [hr, hpabs, hqR]
    have e : (N : ℝ) * (1 - (gradLift N X (i + p) - gradLift N X i)) =
        (N : ℝ) * (gradLift N X i + 1 - gradLift N X (i + p)) := by ring
    rw [e]
    exact harc2.1
  · obtain ⟨p, hp⟩ := Int.eq_ofNat_of_zero_le (neg_nonneg.mpr hk0)
    have hsum : i + k + (p : ℤ) = i := by omega
    have harc1 := gradEvent_arc_bounds hev (i + k) p (fun _ _ _ => Or.inl hfull)
    rw [hsum] at harc1
    have hpN : (p : ℤ) ≤ (N : ℤ) := by
      have := le_abs_self k
      have := neg_abs_le k
      linarith
    obtain ⟨q, hq⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ (N : ℤ) - (p : ℤ))
    have harc2 := gradEvent_arc_bounds hev i q (fun _ _ _ => Or.inl hfull)
    have hend : i + (q : ℤ) = i + k + (N : ℤ) := by omega
    rw [hend, hper (i + k)] at harc2
    have hqR : (N : ℝ) - (p : ℝ) = (q : ℝ) := by
      have : (N : ℤ) - (p : ℤ) = (q : ℤ) := by omega
      exact_mod_cast this
    have hnn : 0 ≤ (N : ℝ) * (gradLift N X i - gradLift N X (i + k)) :=
      le_trans (mul_nonneg hK0 (Nat.cast_nonneg p)) harc1.1
    have hr : |gradLift N X (i + k) - gradLift N X i| =
        gradLift N X i - gradLift N X (i + k) := by
      rw [abs_sub_comm]
      exact abs_of_nonneg (nonneg_of_mul_nonneg_right (by linarith [hnn]) hNpos)
    have hkabs : |(k : ℝ)| = (p : ℝ) := by
      have hk' : (k : ℝ) = -(p : ℝ) := by
        have hk'' : k = -(p : ℤ) := by omega
        rw [hk'']
        push_cast
        ring
      rw [hk', abs_neg, abs_of_nonneg (Nat.cast_nonneg p)]
    rw [hr, hkabs, hqR]
    have e : (N : ℝ) * (1 - (gradLift N X i - gradLift N X (i + k))) =
        (N : ℝ) * (gradLift N X (i + k) + 1 - gradLift N X i) := by ring
    rw [e]
    exact harc2.1

/-- Labels of the window `γ` form a subset of the labels of the window `2γ` as soon as the
window `2γ` is partial, and the pair hypothesis of the good event passes from `γ` to `2γ`. -/
lemma loop_pair_window_two {ℓ γ : ℝ} {N : ℕ+} (hK : 1 ≤ (N : ℝ) * ℓ) (hγ : 0 ≤ γ) {i j : ℤ}
    (hi : ¬GradPartial N ℓ γ ∨ (i ∈ gradLabels N ℓ γ ∧ j ∈ gradLabels N ℓ γ)) :
    ¬GradPartial N ℓ (2 * γ) ∨ (i ∈ gradLabels N ℓ (2 * γ) ∧ j ∈ gradLabels N ℓ (2 * γ)) := by
  by_cases hP2 : GradPartial N ℓ (2 * γ)
  · have hMle : gradM N ℓ γ ≤ gradM N ℓ (2 * γ) := by
      unfold gradM
      exact Real.rpow_le_rpow_of_exponent_le hK (by linarith)
    have hPγ : GradPartial N ℓ γ := by
      by_contra hnot
      have h1 : (N : ℝ) / 8 ≤ gradM N ℓ γ := not_lt.mp hnot
      have h2 : gradM N ℓ (2 * γ) < (N : ℝ) / 8 := hP2
      linarith
    rcases hi with h | ⟨hi0, hj0⟩
    · exact absurd hPγ h
    · right
      have hfl : ⌊gradM N ℓ γ⌋ ≤ ⌊gradM N ℓ (2 * γ)⌋ := Int.floor_le_floor hMle
      have hi1 := (mem_gradLabels_partial hPγ i).1 hi0
      have hj1 := (mem_gradLabels_partial hPγ j).1 hj0
      exact ⟨(mem_gradLabels_partial hP2 i).2 ⟨by omega, by omega⟩,
        (mem_gradLabels_partial hP2 j).2 ⟨by omega, by omega⟩⟩
  · exact Or.inl hP2

/-- The anchor `X 0 = 0` makes the lift at the label `0` vanish. -/
lemma gradLift_zero_of_anchor {N : ℕ+} {X : Fin (N : ℕ) → ℝ} (hX : X ⟨0, N.pos⟩ = 0) :
    gradLift N X 0 = 0 := by
  have hidx : gradIndex N 0 = ⟨0, N.pos⟩ := Fin.ext (by simp [gradIndex])
  unfold gradLift
  rw [hidx, hX]
  simp

end

end Riesz1

end
