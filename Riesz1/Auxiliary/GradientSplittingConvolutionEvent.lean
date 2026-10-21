/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingWindowDefs

/-!
# The event `𝒜_{ε,γ}`, microscopic comparison and packing

The data part of Lemma 5.7 (the event `𝒜_{ε,γ}`) and the particle-level claims of
the convolution part of Lemma 5.7: on `𝒜_{ε,γ}`, microscopic unit intervals contain at most
`2 + K^ε` particles of the window, and `K^{-ε} d(i,j) ≤ N dist(x_i,x_j) ≤ K^ε d(i,j)` for labels
`i, j` of the window.

Conventions, as in `GradientSplittingWindowDefs.lean`: `K = Nℓ`, `M = K^γ`, `n = ⌊M⌋`, the lifts are
`gradLift N X j` with `x_{j+N} = x_j + 1`, and `d(i,j) = min(|j-i|, N-|j-i|)`
(`gradLabelDist`). In a partial window the labels are `-n, …, n`. In a full window every
integer is admissible, because indices are cyclic.

The event is a subset of the configuration space. The inequalities below define it, as the
paper does. The comparison and packing proofs use only the edge bounds and the first bound of
the event.
-/

@[expose] public section

open Finset

namespace Riesz1

noncomputable section

/-- The label distance `d(i,j) = min(|j-i|, N-|j-i|)`, on integer labels. -/
def gradLabelDist (N : ℕ+) (i j : ℤ) : ℤ := min |j - i| ((N : ℤ) - |j - i|)

/-- A label `j` is admissible in the window. In a partial window it must lie in `I`. A full window
is cyclic, so every integer is admissible. -/
def gradInWindow (N : ℕ+) (ℓ γ : ℝ) (j : ℤ) : Prop :=
  GradPartial N ℓ γ → j ∈ gradLabels N ℓ γ

/-- The event `𝒜_{ε,γ}` of the data part of Lemma 5.7, for `X ∈ ℝ^N` with `K = Nℓ`:
`|N(x_{i+k} - x_i) - k| ≤ K^ε |k|^{s/2}` whenever `i, i+k ∈ I` and `0 < |k| ≤ ⌊N/2⌋`, and
`K^{-ε} ≤ N(x_{i+1} - x_i) ≤ K^ε` whenever `i, i+1 ∈ I`. -/
def gradEvent (s γ ε : ℝ) (N : ℕ+) (ℓ : ℝ) (X : Fin (N : ℕ) → ℝ) : Prop :=
  (∀ i ∈ gradLabels N ℓ γ, ∀ k : ℤ, gradInWindow N ℓ γ (i + k) → k ≠ 0 → 2 * |k| ≤ (N : ℤ) →
      |(N : ℝ) * (gradLift N X (i + k) - gradLift N X i) - k| ≤
        ((N : ℝ) * ℓ) ^ ε * |(k : ℝ)| ^ (s / 2)) ∧
  (∀ i ∈ gradLabels N ℓ γ, gradInWindow N ℓ γ (i + 1) →
      ((N : ℝ) * ℓ) ^ (-ε) ≤ (N : ℝ) * (gradLift N X (i + 1) - gradLift N X i) ∧
        (N : ℝ) * (gradLift N X (i + 1) - gradLift N X i) ≤ ((N : ℝ) * ℓ) ^ ε)

/-- Membership in the labels of a partial window: `I = {-n, …, n}`. -/
lemma mem_gradLabels_partial {ℓ γ : ℝ} {N : ℕ+} (hP : GradPartial N ℓ γ) (j : ℤ) :
    j ∈ gradLabels N ℓ γ ↔ -⌊gradM N ℓ γ⌋ ≤ j ∧ j ≤ ⌊gradM N ℓ γ⌋ := by
  unfold gradLabels
  simp only [hP, ite_true, Finset.mem_Icc]

/-- Membership in the labels of a full window: `I = {0, …, N-1}`. -/
lemma mem_gradLabels_full {ℓ γ : ℝ} {N : ℕ+} (hP : ¬GradPartial N ℓ γ) (j : ℤ) :
    j ∈ gradLabels N ℓ γ ↔ 0 ≤ j ∧ j < (N : ℤ) := by
  unfold gradLabels
  simp only [hP, ite_false, Finset.mem_Ico]

/-! ## Periodicity of the lifts and chains of edges -/

/-- Shifting a label by `N m` shifts its lift by `m`: `x_{j+Nm} = x_j + m`. -/
lemma gradLift_add_mul (N : ℕ+) (X : Fin (N : ℕ) → ℝ) (j m : ℤ) :
    gradLift N X (j + N * m) = gradLift N X j + m := by
  unfold gradLift
  have hidx : gradIndex N (j + N * m) = gradIndex N j := by
    apply Fin.ext
    simp only [gradIndex, Int.add_mul_emod_self_left]
  have hdiv : (j + (N : ℤ) * m) / (N : ℤ) = j / (N : ℤ) + m := by
    rw [Int.add_mul_ediv_left _ _ (by exact_mod_cast N.ne_zero)]
  rw [hidx, hdiv]
  push_cast
  ring

/-- A chain of `t` edges, each with increment in `[lo, hi]`, has total increment in `[lo t, hi t]`. -/
lemma gradChain_bounds (f : ℤ → ℝ) (p : ℤ) (lo hi : ℝ) (t : ℕ)
    (h : ∀ l : ℤ, p ≤ l → l < p + t → lo ≤ f (l + 1) - f l ∧ f (l + 1) - f l ≤ hi) :
    lo * t ≤ f (p + t) - f p ∧ f (p + t) - f p ≤ hi * t := by
  induction t with
  | zero => simp
  | succ t ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun l h1 h2 => h l h1 (by omega))
    obtain ⟨h1, h2⟩ := h (p + t) (by omega) (by push_cast; omega)
    have e : p + ((t + 1 : ℕ) : ℤ) = p + t + 1 := by push_cast; ring
    rw [e]
    push_cast
    have hl : lo * ((t : ℝ) + 1) = lo * t + lo := by ring
    have hh : hi * ((t : ℝ) + 1) = hi * t + hi := by ring
    constructor <;> linarith

/-- Edge bounds along the integer interval `[a, b)` give bounds on the total increment `f b - f a`. -/
lemma gradEdge_chain {f : ℤ → ℝ} {lo hi : ℝ} {a b : ℤ} (hab : a ≤ b)
    (hedge : ∀ l : ℤ, a ≤ l → l < b → lo ≤ f (l + 1) - f l ∧ f (l + 1) - f l ≤ hi) :
    lo * ((b - a : ℤ) : ℝ) ≤ f b - f a ∧ f b - f a ≤ hi * ((b - a : ℤ) : ℝ) := by
  obtain ⟨t, ht⟩ : ∃ t : ℕ, b = a + t := ⟨(b - a).toNat, by omega⟩
  subst ht
  have e : a + (t : ℤ) - a = (t : ℤ) := by ring
  rw [e]
  push_cast
  exact gradChain_bounds f a lo hi t hedge

/-! ## Edge bounds of the event -/

/-- On a full window every edge is controlled by the event, for every integer label, by
periodicity of the lifts. -/
lemma gradEdge_full {s γ ε ℓ : ℝ} {N : ℕ+} {X : Fin (N : ℕ) → ℝ}
    (hP : ¬GradPartial N ℓ γ) (hX : gradEvent s γ ε N ℓ X) (l : ℤ) :
    ((N : ℝ) * ℓ) ^ (-ε) ≤ (N : ℝ) * (gradLift N X (l + 1) - gradLift N X l) ∧
      (N : ℝ) * (gradLift N X (l + 1) - gradLift N X l) ≤ ((N : ℝ) * ℓ) ^ ε := by
  have hN : (0 : ℤ) < (N : ℤ) := by exact_mod_cast N.pos
  have hl : l = l % (N : ℤ) + (N : ℤ) * (l / (N : ℤ)) := by rw [Int.emod_def]; ring
  have hi0 : 0 ≤ l % (N : ℤ) := Int.emod_nonneg _ hN.ne'
  have hi1 : l % (N : ℤ) < (N : ℤ) := Int.emod_lt_of_pos _ hN
  have hmem : l % (N : ℤ) ∈ gradLabels N ℓ γ := (mem_gradLabels_full hP _).mpr ⟨hi0, hi1⟩
  have hin : gradInWindow N ℓ γ (l % (N : ℤ) + 1) := fun hPart => absurd hPart hP
  obtain ⟨h1, h2⟩ := hX.2 (l % (N : ℤ)) hmem hin
  have hL0 : gradLift N X l = gradLift N X (l % (N : ℤ)) + ((l / (N : ℤ) : ℤ) : ℝ) := by
    have h := gradLift_add_mul N X (l % (N : ℤ)) (l / (N : ℤ))
    rw [← hl] at h
    exact h
  have hL1 : gradLift N X (l + 1) = gradLift N X (l % (N : ℤ) + 1) + ((l / (N : ℤ) : ℤ) : ℝ) := by
    have h := gradLift_add_mul N X (l % (N : ℤ) + 1) (l / (N : ℤ))
    have e2 : l % (N : ℤ) + 1 + (N : ℤ) * (l / (N : ℤ)) = l + 1 := by linarith [hl]
    rw [e2] at h
    exact h
  have e : gradLift N X (l + 1) - gradLift N X l
      = gradLift N X (l % (N : ℤ) + 1) - gradLift N X (l % (N : ℤ)) := by
    rw [hL1, hL0]
    ring
  rw [e]
  exact ⟨h1, h2⟩

/-- On a partial window, the edges inside `I` are controlled by the event. -/
lemma gradEdge_partial_chain {s γ ε ℓ : ℝ} {N : ℕ+} {X : Fin (N : ℕ) → ℝ}
    (hX : gradEvent s γ ε N ℓ X) {a b : ℤ} (hab : a ≤ b)
    (ha : a ∈ gradLabels N ℓ γ) (hb : b ∈ gradLabels N ℓ γ) (hP : GradPartial N ℓ γ) :
    ((N : ℝ) * ℓ) ^ (-ε) * ((b - a : ℤ) : ℝ) ≤
        (N : ℝ) * (gradLift N X b - gradLift N X a) ∧
      (N : ℝ) * (gradLift N X b - gradLift N X a) ≤
        ((N : ℝ) * ℓ) ^ ε * ((b - a : ℤ) : ℝ) := by
  have hI : ∀ l : ℤ, a ≤ l → l < b →
      ((N : ℝ) * ℓ) ^ (-ε) ≤ (N : ℝ) * (gradLift N X (l + 1) - gradLift N X l) ∧
        (N : ℝ) * (gradLift N X (l + 1) - gradLift N X l) ≤ ((N : ℝ) * ℓ) ^ ε := by
    intro l h1 h2
    rw [mem_gradLabels_partial hP] at ha hb
    have hlI : l ∈ gradLabels N ℓ γ := by
      rw [mem_gradLabels_partial hP]
      constructor <;> omega
    have hl1 : gradInWindow N ℓ γ (l + 1) := by
      intro _
      rw [mem_gradLabels_partial hP]
      constructor <;> omega
    exact (hX.2 l hlI hl1)
  have hk := gradEdge_chain (f := fun l => (N : ℝ) * gradLift N X l)
    (lo := ((N : ℝ) * ℓ) ^ (-ε)) (hi := ((N : ℝ) * ℓ) ^ ε) hab ?_
  · obtain ⟨k1, k2⟩ := hk
    constructor
    · rw [mul_sub]; exact k1
    · rw [mul_sub]; exact k2
  · intro l h1 h2
    obtain ⟨e1, e2⟩ := hI l h1 h2
    constructor
    · show _ ≤ (N : ℝ) * gradLift N X (l + 1) - (N : ℝ) * gradLift N X l
      rw [← mul_sub]; exact e1
    · show (N : ℝ) * gradLift N X (l + 1) - (N : ℝ) * gradLift N X l ≤ _
      rw [← mul_sub]; exact e2

/-! ## Partial-window arithmetic -/

/-- In a partial window, `8n < N` for `n = ⌊M⌋`, since `n ≤ M < N/8`. -/
lemma gradPartial_eight_mul_lt {ℓ γ : ℝ} {N : ℕ+} (hP : GradPartial N ℓ γ) :
    8 * ⌊gradM N ℓ γ⌋ < (N : ℤ) := by
  have h1 : ((⌊gradM N ℓ γ⌋ : ℤ) : ℝ) ≤ gradM N ℓ γ := Int.floor_le _
  have h2 : (8 : ℝ) * gradM N ℓ γ < N := by linarith
  have h3 : ((8 * ⌊gradM N ℓ γ⌋ : ℤ) : ℝ) < ((N : ℤ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast h3

/-- The power bound `K^ε ≤ x^{1-s/2}` when `K^γ ≤ x` and `x ≥ 1`, from `ε < (1 - s/2)/8` and
`γ > 1`. -/
lemma gradK_rpow_le {s γ ε K x : ℝ} (hγ : 1 < γ) (hε : 0 < ε)
    (hεs : ε < (1 - s / 2) / 8) (hK : 1 ≤ K) (hx : 1 ≤ x) (hKx : K ^ γ ≤ x) :
    K ^ ε ≤ x ^ (1 - s / 2) := by
  have hK0 : 0 < K := by linarith
  have hγ0 : 0 < γ := by linarith
  have hKγ : K ^ ε = (K ^ γ) ^ (ε / γ) := by
    rw [← Real.rpow_mul hK0.le]
    congr 1
    field_simp
  have hle : ε / γ ≤ 1 - s / 2 := by
    have h1 : ε / γ ≤ ε := div_le_self hε.le hγ.le
    linarith
  rw [hKγ]
  calc (K ^ γ) ^ (ε / γ) ≤ x ^ (ε / γ) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hK0.le γ) hKx (div_nonneg hε.le hγ0.le)
    _ ≤ x ^ (1 - s / 2) := Real.rpow_le_rpow_of_exponent_le hx hle

/-- For `n ≥ 1` and `|k| ≤ 2n`, the event's power factor satisfies `K^ε |k|^{s/2} ≤ 2n` when
`K^γ ≤ 2n`. -/
lemma gradK_mul_rpow_le {s γ ε K : ℝ} (hs0 : 0 < s) (hγ : 1 < γ) (hε : 0 < ε)
    (hεs : ε < (1 - s / 2) / 8) (hK : 1 ≤ K) {n t : ℝ} (hn : 1 ≤ n) (hKn : K ^ γ ≤ 2 * n)
    (ht0 : 0 ≤ t) (ht : t ≤ 2 * n) :
    K ^ ε * t ^ (s / 2) ≤ 2 * n := by
  have hx : (1 : ℝ) ≤ 2 * n := by linarith
  have hpos : (0 : ℝ) < 2 * n := by linarith
  have h1 : K ^ ε ≤ (2 * n) ^ (1 - s / 2) := gradK_rpow_le hγ hε hεs hK hx hKn
  have h2 : t ^ (s / 2) ≤ (2 * n) ^ (s / 2) :=
    Real.rpow_le_rpow ht0 ht (by linarith)
  have hK0 : 0 ≤ K ^ ε := Real.rpow_nonneg (by linarith) ε
  calc K ^ ε * t ^ (s / 2) ≤ (2 * n) ^ (1 - s / 2) * (2 * n) ^ (s / 2) :=
        mul_le_mul h1 h2 (Real.rpow_nonneg ht0 _) (Real.rpow_nonneg hpos.le _)
    _ = 2 * n := by
        rw [← Real.rpow_add hpos]
        norm_num

/-- The full-length `K^γ = M` bound: `K^γ ≤ 2 ⌊M⌋` when `⌊M⌋ ≥ 1`. -/
lemma gradM_le_two_floor {ℓ γ : ℝ} {N : ℕ+} (hn : 1 ≤ ⌊gradM N ℓ γ⌋) :
    ((N : ℝ) * ℓ) ^ γ ≤ 2 * (⌊gradM N ℓ γ⌋ : ℝ) := by
  have h1 : gradM N ℓ γ < (⌊gradM N ℓ γ⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have h2 : (1 : ℝ) ≤ (⌊gradM N ℓ γ⌋ : ℝ) := by exact_mod_cast hn
  have h3 : gradM N ℓ γ = ((N : ℝ) * ℓ) ^ γ := rfl
  rw [← h3]
  linarith

/-- In a partial window, two labels of `I` have microscopic separation at most `4n`:
`|N(x_j - x_i)| ≤ 4n`. -/
lemma gradPartial_lift_bound {s γ ε ℓ : ℝ} {N : ℕ+} {X : Fin (N : ℕ) → ℝ}
    (hs0 : 0 < s) (hγ : 1 < γ) (hε : 0 < ε) (hεs : ε < (1 - s / 2) / 8)
    (hK : 1 ≤ (N : ℝ) * ℓ) (hX : gradEvent s γ ε N ℓ X) (hP : GradPartial N ℓ γ)
    {i j : ℤ} (hi : i ∈ gradLabels N ℓ γ) (hj : j ∈ gradLabels N ℓ γ) :
    |(N : ℝ) * (gradLift N X j - gradLift N X i)| ≤ 4 * (⌊gradM N ℓ γ⌋ : ℝ) := by
  have hi' := (mem_gradLabels_partial hP i).mp hi
  have hj' := (mem_gradLabels_partial hP j).mp hj
  have hn0 : (0 : ℤ) ≤ ⌊gradM N ℓ γ⌋ := by omega
  have hn0R : (0 : ℝ) ≤ (⌊gradM N ℓ γ⌋ : ℝ) := by exact_mod_cast hn0
  by_cases hij : j = i
  · subst hij
    rw [sub_self, mul_zero, abs_zero]
    linarith
  · have hk : j - i ≠ 0 := sub_ne_zero.mpr hij
    have hkb : |j - i| ≤ 2 * ⌊gradM N ℓ γ⌋ := by
      rw [abs_le]
      constructor <;> omega
    have hk1 : 1 ≤ |j - i| := Int.one_le_abs hk
    have hn1 : 1 ≤ ⌊gradM N ℓ γ⌋ := by omega
    have h8 := gradPartial_eight_mul_lt hP
    have hkR : |((j - i : ℤ) : ℝ)| ≤ 2 * (⌊gradM N ℓ γ⌋ : ℝ) := by
      rw [← Int.cast_abs]
      exact_mod_cast hkb
    have hKγ := gradM_le_two_floor (N := N) (ℓ := ℓ) (γ := γ) hn1
    have hfirst := hX.1 i hi (j - i)
      (fun _ => by rw [show i + (j - i) = j by ring]; exact hj) hk (by omega)
    rw [show i + (j - i) = j by ring] at hfirst
    have hpow := gradK_mul_rpow_le hs0 hγ hε hεs hK
      (n := (⌊gradM N ℓ γ⌋ : ℝ)) (by exact_mod_cast hn1) hKγ (abs_nonneg _) hkR
    have hnum : |((j - i : ℤ) : ℝ)| ≤ 2 * (⌊gradM N ℓ γ⌋ : ℝ) := hkR
    have htri : |(N : ℝ) * (gradLift N X j - gradLift N X i)| ≤
        |(N : ℝ) * (gradLift N X j - gradLift N X i) - ((j - i : ℤ) : ℝ)| +
          |((j - i : ℤ) : ℝ)| := by
      have := abs_add_le ((N : ℝ) * (gradLift N X j - gradLift N X i) - ((j - i : ℤ) : ℝ))
        ((j - i : ℤ) : ℝ)
      simpa using this
    have hpow' : |(N : ℝ) * (gradLift N X j - gradLift N X i) - ((j - i : ℤ) : ℝ)| ≤
        2 * (⌊gradM N ℓ γ⌋ : ℝ) := by
      have hfirst' := hfirst
      rw [show ((j - i : ℤ) : ℝ) = ((j - i : ℤ) : ℝ) from rfl] at hfirst'
      exact le_trans hfirst' hpow
    linarith

/-! ## Comparison with the circular distance -/

/-- On `[0, 1]`, the circular distance to `ℤ` is `min D (1 - D)`. -/
lemma circDist_one_eq_min {D : ℝ} (h0 : 0 ≤ D) (h1 : D ≤ 1) :
    circDist 1 D = min D (1 - D) := by
  unfold circDist
  rcases lt_or_ge D (1 / 2) with hD | hD
  · have hr : round (D / 1) = 0 := by
      rw [div_one, round_eq, Int.floor_eq_zero_iff, Set.mem_Ico]
      constructor <;> linarith
    rw [hr, Int.cast_zero, mul_zero, sub_zero, abs_of_nonneg h0,
      min_eq_left (by linarith : D ≤ 1 - D)]
  · have hr : round (D / 1) = 1 := by
      rw [div_one, round_eq, Int.floor_eq_iff]
      push_cast
      constructor <;> linarith
    rw [hr, Int.cast_one, one_mul, abs_of_nonpos (by linarith : D - 1 ≤ 0),
      min_eq_right (by linarith : 1 - D ≤ D)]
    ring

/-- Scaled edge chain: if each edge increment of `N x` lies in `[lo, hi]`, so does the total. -/
lemma gradScaled_chain {ε ℓ : ℝ} {N : ℕ+} {X : Fin (N : ℕ) → ℝ} {a b : ℤ} (hab : a ≤ b)
    (hedge : ∀ l : ℤ, a ≤ l → l < b →
      ((N : ℝ) * ℓ) ^ (-ε) ≤ (N : ℝ) * (gradLift N X (l + 1) - gradLift N X l) ∧
        (N : ℝ) * (gradLift N X (l + 1) - gradLift N X l) ≤ ((N : ℝ) * ℓ) ^ ε) :
    ((N : ℝ) * ℓ) ^ (-ε) * ((b - a : ℤ) : ℝ) ≤ (N : ℝ) * (gradLift N X b - gradLift N X a) ∧
      (N : ℝ) * (gradLift N X b - gradLift N X a) ≤ ((N : ℝ) * ℓ) ^ ε * ((b - a : ℤ) : ℝ) := by
  have hk := gradEdge_chain (f := fun l => (N : ℝ) * gradLift N X l)
    (lo := ((N : ℝ) * ℓ) ^ (-ε)) (hi := ((N : ℝ) * ℓ) ^ ε) hab ?_
  · obtain ⟨k1, k2⟩ := hk
    constructor
    · rw [mul_sub]; exact k1
    · rw [mul_sub]; exact k2
  · intro l h1 h2
    obtain ⟨e1, e2⟩ := hedge l h1 h2
    constructor
    · show _ ≤ (N : ℝ) * gradLift N X (l + 1) - (N : ℝ) * gradLift N X l
      rw [← mul_sub]; exact e1
    · show (N : ℝ) * gradLift N X (l + 1) - (N : ℝ) * gradLift N X l ≤ _
      rw [← mul_sub]; exact e2

/-- Comparison on a full window, for labels `i ≤ j` of `{0, …, N-1}`:
`K^{-ε} d(i,j) ≤ N dist(x_i,x_j) ≤ K^ε d(i,j)`. -/
lemma gradComparison_full {s γ ε ℓ : ℝ} {N : ℕ+} {X : Fin (N : ℕ) → ℝ}
    (hK : 1 ≤ (N : ℝ) * ℓ) (hP : ¬GradPartial N ℓ γ) (hX : gradEvent s γ ε N ℓ X)
    {i j : ℤ} (hi : i ∈ gradLabels N ℓ γ) (hj : j ∈ gradLabels N ℓ γ) (hij : i ≤ j) :
    ((N : ℝ) * ℓ) ^ (-ε) * (gradLabelDist N i j : ℝ) ≤
        (N : ℝ) * circDist 1 (gradLift N X j - gradLift N X i) ∧
      (N : ℝ) * circDist 1 (gradLift N X j - gradLift N X i) ≤
        ((N : ℝ) * ℓ) ^ ε * (gradLabelDist N i j : ℝ) := by
  rw [mem_gradLabels_full hP] at hi hj
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hNz : (0 : ℤ) < N := by exact_mod_cast N.pos
  have hK0 : 0 < (N : ℝ) * ℓ := by linarith
  have hd : gradLabelDist N i j = min (j - i) ((N : ℤ) - (j - i)) := by
    unfold gradLabelDist
    rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ j - i)]
  have hedge_all : ∀ l : ℤ, ((N : ℝ) * ℓ) ^ (-ε) ≤ (N : ℝ) * (gradLift N X (l + 1) - gradLift N X l)
      ∧ (N : ℝ) * (gradLift N X (l + 1) - gradLift N X l) ≤ ((N : ℝ) * ℓ) ^ ε :=
    fun l => gradEdge_full hP hX l
  have c := gradScaled_chain (hab := hij) (fun l _ _ => hedge_all l)
  have hij' : j ≤ i + N := by omega
  have e := gradScaled_chain (hab := hij') (fun l _ _ => hedge_all l)
  have hshift : gradLift N X (i + N) = gradLift N X i + 1 := by
    have h := gradLift_add_mul N X i 1
    rw [mul_one, Int.cast_one] at h
    exact h
  obtain ⟨c1, c2⟩ := c
  obtain ⟨e1, e2⟩ := e
  have hcast : ((i + N - j : ℤ) : ℝ) = (N : ℝ) - ((j - i : ℤ) : ℝ) := by push_cast; ring
  rw [hcast] at e1 e2
  have hsh : (N : ℝ) * (gradLift N X (i + N) - gradLift N X j)
      = (N : ℝ) * (1 - (gradLift N X j - gradLift N X i)) := by
    rw [hshift]; ring
  rw [hsh] at e1 e2
  have hA0 : (0 : ℝ) ≤ ((j - i : ℤ) : ℝ) := by
    have : (0 : ℤ) ≤ j - i := by omega
    exact_mod_cast this
  have hNA : (0 : ℝ) ≤ (N : ℝ) - ((j - i : ℤ) : ℝ) := by
    have : (j - i : ℤ) ≤ N := by omega
    have : ((j - i : ℤ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast this
    linarith
  have hKneg : (0 : ℝ) < ((N : ℝ) * ℓ) ^ (-ε) := Real.rpow_pos_of_pos hK0 _
  have hD0 : 0 ≤ gradLift N X j - gradLift N X i := by
    have h1 : 0 ≤ (N : ℝ) * (gradLift N X j - gradLift N X i) :=
      le_trans (mul_nonneg hKneg.le hA0) c1
    exact (mul_nonneg_iff_of_pos_left hN).mp h1
  have hD1 : gradLift N X j - gradLift N X i ≤ 1 := by
    have h1 : 0 ≤ (N : ℝ) * (1 - (gradLift N X j - gradLift N X i)) :=
      le_trans (mul_nonneg hKneg.le hNA) e1
    have h2 := (mul_nonneg_iff_of_pos_left hN).mp h1
    linarith
  have hcastd : ((gradLabelDist N i j : ℤ) : ℝ)
      = min ((j - i : ℤ) : ℝ) (((N : ℤ) - (j - i) : ℤ) : ℝ) := by
    rw [hd, Int.cast_min]
  have hcast2 : (((N : ℤ) - (j - i) : ℤ) : ℝ) = (N : ℝ) - ((j - i : ℤ) : ℝ) := by
    push_cast; ring
  have hKε : (0 : ℝ) < ((N : ℝ) * ℓ) ^ ε := Real.rpow_pos_of_pos hK0 _
  rw [circDist_one_eq_min hD0 hD1, mul_min_of_nonneg _ _ hN.le, hcastd, hcast2]
  constructor
  · rw [mul_min_of_nonneg _ _ hKneg.le]
    exact min_le_min c1 e1
  · rw [mul_min_of_nonneg _ _ hKε.le]
    exact min_le_min c2 e2

/-- The circular distance to `ℤ` is invariant under integer shifts. -/
lemma circDist_one_add_int (u : ℝ) (k : ℤ) : circDist 1 (u + k) = circDist 1 u := by
  unfold circDist
  simp only [div_one, one_mul]
  rw [round_add_intCast]
  push_cast
  congr 1
  ring

/-- The circular distance to `ℤ` is `min (fract x) (1 - fract x)`. -/
lemma circDist_one_eq_fract (x : ℝ) :
    circDist 1 x = min (Int.fract x) (1 - Int.fract x) := by
  rw [← circDist_one_eq_min (Int.fract_nonneg x) (Int.fract_lt_one x).le]
  conv_lhs => rw [← Int.fract_add_floor x]
  rw [circDist_one_add_int]

/-- The circular distance to `ℤ` is invariant under the reflection `x ↦ -x`. -/
lemma circDist_one_neg (x : ℝ) : circDist 1 (-x) = circDist 1 x := by
  rw [circDist_one_eq_fract, circDist_one_eq_fract]
  rcases eq_or_ne (Int.fract x) 0 with h0 | h0
  · rw [Int.fract_neg_eq_zero.mpr h0, h0]
  · rw [Int.fract_neg h0, sub_sub_cancel, min_comm]

/-- The circular distance is symmetric in its two points. -/
lemma circDist_one_sub_comm (u v : ℝ) : circDist 1 (u - v) = circDist 1 (v - u) := by
  have h := circDist_one_neg (u - v)
  rw [show -(u - v) = v - u by ring] at h
  exact h.symm

lemma gradLabelDist_comm (N : ℕ+) (i j : ℤ) : gradLabelDist N i j = gradLabelDist N j i := by
  unfold gradLabelDist
  rw [abs_sub_comm]

/-- Comparison on a partial window, for labels `i ≤ j` of `I = {-n, …, n}`. -/
lemma gradComparison_partial {s γ ε ℓ : ℝ} {N : ℕ+} {X : Fin (N : ℕ) → ℝ}
    (hs0 : 0 < s) (hγ : 1 < γ) (hε : 0 < ε) (hεs : ε < (1 - s / 2) / 8)
    (hK : 1 ≤ (N : ℝ) * ℓ) (hP : GradPartial N ℓ γ) (hX : gradEvent s γ ε N ℓ X)
    {i j : ℤ} (hi : i ∈ gradLabels N ℓ γ) (hj : j ∈ gradLabels N ℓ γ) (hij : i ≤ j) :
    ((N : ℝ) * ℓ) ^ (-ε) * (gradLabelDist N i j : ℝ) ≤
        (N : ℝ) * circDist 1 (gradLift N X j - gradLift N X i) ∧
      (N : ℝ) * circDist 1 (gradLift N X j - gradLift N X i) ≤
        ((N : ℝ) * ℓ) ^ ε * (gradLabelDist N i j : ℝ) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hK0 : 0 < (N : ℝ) * ℓ := by linarith
  have hi' := (mem_gradLabels_partial hP i).mp hi
  have hj' := (mem_gradLabels_partial hP j).mp hj
  have h8 := gradPartial_eight_mul_lt hP
  have hd : gradLabelDist N i j = j - i := by
    unfold gradLabelDist
    rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ j - i),
      min_eq_left (by omega : j - i ≤ (N : ℤ) - (j - i))]
  obtain ⟨c1, c2⟩ := gradEdge_partial_chain hX hij hi hj hP
  have hbd := gradPartial_lift_bound hs0 hγ hε hεs hK hX hP hi hj
  have hA0 : (0 : ℝ) ≤ ((j - i : ℤ) : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) ≤ j - i)
  have hKneg : (0 : ℝ) < ((N : ℝ) * ℓ) ^ (-ε) := Real.rpow_pos_of_pos hK0 _
  have hD0 : 0 ≤ gradLift N X j - gradLift N X i := by
    have h1 : 0 ≤ (N : ℝ) * (gradLift N X j - gradLift N X i) :=
      le_trans (mul_nonneg hKneg.le hA0) c1
    exact (mul_nonneg_iff_of_pos_left hN).mp h1
  have h8R : (8 : ℝ) * ⌊gradM N ℓ γ⌋ < N := by exact_mod_cast h8
  have hDhalf : gradLift N X j - gradLift N X i ≤ 1 / 2 := by
    have h1 := (abs_le.mp hbd).2
    have h2 : (N : ℝ) * (gradLift N X j - gradLift N X i) ≤ (N : ℝ) * (1 / 2) := by linarith
    exact le_of_mul_le_mul_left h2 hN
  rw [circDist_of_mem_Icc (by norm_num : (0 : ℝ) < 1) hD0 (by linarith), hd]
  exact ⟨c1, c2⟩

/-- Comparison `K^{-ε} d(i,j) ≤ N dist(x_i,x_j) ≤ K^ε d(i,j)` for all labels `i, j` of the
window, on the event `𝒜_{ε,γ}`. The distance `dist` is the circular distance on `ℝ/ℤ`. -/
theorem gradient_splitting_comparison {s γ ε ℓ : ℝ} {N : ℕ+} {X : Fin (N : ℕ) → ℝ}
    (hs0 : 0 < s) (hγ : 1 < γ) (hε : 0 < ε) (hεs : ε < (1 - s / 2) / 8)
    (hK : 1 ≤ (N : ℝ) * ℓ) (hX : gradEvent s γ ε N ℓ X)
    {i j : ℤ} (hi : i ∈ gradLabels N ℓ γ) (hj : j ∈ gradLabels N ℓ γ) :
    ((N : ℝ) * ℓ) ^ (-ε) * (gradLabelDist N i j : ℝ) ≤
        (N : ℝ) * circDist 1 (gradLift N X j - gradLift N X i) ∧
      (N : ℝ) * circDist 1 (gradLift N X j - gradLift N X i) ≤
        ((N : ℝ) * ℓ) ^ ε * (gradLabelDist N i j : ℝ) := by
  by_cases hP : GradPartial N ℓ γ
  · rcases le_total i j with hij | hij
    · exact gradComparison_partial hs0 hγ hε hεs hK hP hX hi hj hij
    · have h := gradComparison_partial hs0 hγ hε hεs hK hP hX hj hi hij
      rw [gradLabelDist_comm N i j, circDist_one_sub_comm]
      exact h
  · rcases le_total i j with hij | hij
    · exact gradComparison_full hK hP hX hi hj hij
    · have h := gradComparison_full hK hP hX hj hi hij
      rw [gradLabelDist_comm N i j, circDist_one_sub_comm]
      exact h

/-! ## Packing -/

/-- A finite set of integers whose images under `g` are `δ`-separated and lie within distance one
has fewer than `1 + 1/δ` elements. -/
lemma card_lt_of_gap (T : Finset ℤ) (hT : T.Nonempty) (g : ℤ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ a ∈ T, ∀ b ∈ T, a ≤ b → δ * ((b - a : ℤ) : ℝ) ≤ g b - g a)
    (hdiam : ∀ a ∈ T, ∀ b ∈ T, g b - g a < 1) :
    (T.card : ℝ) < 1 + 1 / δ := by
  have haT : T.min' hT ∈ T := Finset.min'_mem T hT
  have hbT : T.max' hT ∈ T := Finset.max'_mem T hT
  have hab : T.min' hT ≤ T.max' hT := Finset.min'_le T _ hbT
  have hsub : T ⊆ Finset.Icc (T.min' hT) (T.max' hT) := fun t ht =>
    Finset.mem_Icc.mpr ⟨Finset.min'_le T t ht, Finset.le_max' T t ht⟩
  have hcard : T.card ≤ (T.max' hT + 1 - T.min' hT).toNat := by
    have := Finset.card_le_card hsub
    rw [Int.card_Icc] at this
    exact this
  have hsep' := hsep _ haT _ hbT hab
  have hdiam' := hdiam _ haT _ hbT
  have hlt : ((T.max' hT - T.min' hT : ℤ) : ℝ) < 1 / δ := by
    rw [lt_div_iff₀ hδ]
    have := mul_comm δ ((T.max' hT - T.min' hT : ℤ) : ℝ)
    linarith
  have hnn : (0 : ℤ) ≤ T.max' hT + 1 - T.min' hT := by omega
  have hcardZ : (T.card : ℤ) ≤ T.max' hT + 1 - T.min' hT := by
    have := Int.toNat_of_nonneg hnn
    omega
  have hcardR : ((T.card : ℤ) : ℝ) ≤ ((T.max' hT + 1 - T.min' hT : ℤ) : ℝ) := by
    exact_mod_cast hcardZ
  push_cast at hcardR hlt ⊢
  linarith

/-- Packing on `𝒜_{ε,γ}` (convolution part of Lemma 5.7): a set `T` of labels of
the window whose microscopic positions `N x_j` lie in one microscopic unit interval has at most
`2 + K^ε` elements. Here the unit intervals are the arcs `[c + mN, c + mN + 1)` of `ℝ/Nℤ`. -/
theorem gradient_splitting_packing {s γ ε ℓ : ℝ} {N : ℕ+} {X : Fin (N : ℕ) → ℝ}
    (hs0 : 0 < s) (hγ : 1 < γ) (hε : 0 < ε) (hεs : ε < (1 - s / 2) / 8)
    (hK : 1 ≤ (N : ℝ) * ℓ) (hN : (2 : ℕ) ≤ (N : ℕ)) (hX : gradEvent s γ ε N ℓ X)
    (c : ℝ) {T : Finset ℤ} (hT : T ⊆ gradLabels N ℓ γ)
    (hTc : ∀ j ∈ T, ∃ m : ℤ, c + (N : ℝ) * (m : ℝ) ≤ (N : ℝ) * gradLift N X j ∧
      (N : ℝ) * gradLift N X j < c + (N : ℝ) * (m : ℝ) + 1) :
    (T.card : ℝ) ≤ 2 + ((N : ℝ) * ℓ) ^ ε := by
  have hK0 : 0 < (N : ℝ) * ℓ := by linarith
  have hKε : 0 < ((N : ℝ) * ℓ) ^ ε := Real.rpow_pos_of_pos hK0 _
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hδ : (0 : ℝ) < ((N : ℝ) * ℓ) ^ (-ε) := Real.rpow_pos_of_pos hK0 _
  have hinv : 1 / ((N : ℝ) * ℓ) ^ (-ε) = ((N : ℝ) * ℓ) ^ ε := by
    rw [Real.rpow_neg hK0.le, one_div, inv_inv]
  rcases T.eq_empty_or_nonempty with hE | hne
  · rw [hE, Finset.card_empty]
    push_cast
    linarith
  by_cases hP : GradPartial N ℓ γ
  · have hn0 : (0 : ℤ) ≤ ⌊gradM N ℓ γ⌋ := Int.floor_nonneg.mpr (by unfold gradM; positivity)
    rcases eq_or_lt_of_le hn0 with h0 | h1
    · -- the window is `{0}`
      have hsub : T ⊆ {0} := by
        intro t ht
        have := (mem_gradLabels_partial hP t).mp (hT ht)
        rw [Finset.mem_singleton]
        omega
      have hcard : T.card ≤ 1 := le_trans (Finset.card_le_card hsub) (by simp)
      have : (T.card : ℝ) ≤ 1 := by exact_mod_cast hcard
      linarith
    · have hn1 : 1 ≤ ⌊gradM N ℓ γ⌋ := h1
      have h8 : (8 : ℝ) * ⌊gradM N ℓ γ⌋ < N := by exact_mod_cast gradPartial_eight_mul_lt hP
      choose! m hm using hTc
      -- all particles of `T` lie in one arc: distinct arcs are `N - 1` apart
      have hone : ∀ j ∈ T, ∀ j' ∈ T, m j < m j' → False := by
        intro j hj j' hj' hlt
        have hb := gradPartial_lift_bound hs0 hγ hε hεs hK hX hP (hT hj) (hT hj')
        have hb' := (abs_le.mp hb).2
        have hmR : (m j : ℝ) + 1 ≤ (m j' : ℝ) := by
          exact_mod_cast (show m j + 1 ≤ m j' by omega)
        have hNm : (N : ℝ) * (m j : ℝ) + N ≤ (N : ℝ) * (m j' : ℝ) := by
          have h := mul_le_mul_of_nonneg_left hmR hNpos.le
          rw [mul_add, mul_one] at h
          exact h
        linarith [(hm j hj).2, (hm j' hj').1]
      obtain ⟨j0, hj0⟩ := id hne
      have hm0 : ∀ j ∈ T, m j = m j0 := by
        intro j hj
        rcases lt_trichotomy (m j) (m j0) with h | h | h
        · exact (hone j hj j0 hj0 h).elim
        · exact h
        · exact (hone j0 hj0 j hj h).elim
      have hbox : ∀ j ∈ T, c + (N : ℝ) * (m j0 : ℝ) ≤ (N : ℝ) * gradLift N X j ∧
          (N : ℝ) * gradLift N X j < c + (N : ℝ) * (m j0 : ℝ) + 1 := by
        intro j hj
        have h := hm j hj
        rw [hm0 j hj] at h
        exact h
      have hsep : ∀ a ∈ T, ∀ b ∈ T, a ≤ b →
          ((N : ℝ) * ℓ) ^ (-ε) * ((b - a : ℤ) : ℝ) ≤
            (N : ℝ) * gradLift N X b - (N : ℝ) * gradLift N X a := by
        intro a ha b hb hab
        have h := (gradEdge_partial_chain hX hab (hT ha) (hT hb) hP).1
        rwa [mul_sub] at h
      have hdiam : ∀ a ∈ T, ∀ b ∈ T,
          (N : ℝ) * gradLift N X b - (N : ℝ) * gradLift N X a < 1 := by
        intro a ha b hb
        linarith [(hbox a ha).1, (hbox a ha).2, (hbox b hb).1, (hbox b hb).2]
      have hgap := card_lt_of_gap T hne (fun t => (N : ℝ) * gradLift N X t)
        (((N : ℝ) * ℓ) ^ (-ε)) hδ hsep hdiam
      rw [hinv] at hgap
      linarith
  · -- full window: the cyclic shifts `j ↦ j - N m_j` are distinct and lie in one arc
    choose! m hm using hTc
    have hNZ : (0 : ℤ) < N := by exact_mod_cast N.pos
    have hinj : Set.InjOn (fun j : ℤ => j - (N : ℤ) * m j) (T : Set ℤ) := by
      intro j hj j' hj' heq
      obtain ⟨hj0, hjN⟩ := (mem_gradLabels_full hP j).mp (hT hj)
      obtain ⟨hj0', hjN'⟩ := (mem_gradLabels_full hP j').mp (hT hj')
      have heq' : j - (N : ℤ) * m j = j' - (N : ℤ) * m j' := heq
      have key : j - j' = (N : ℤ) * (m j - m j') := by linear_combination heq'
      rcases lt_trichotomy (m j) (m j') with h | h | h
      · exfalso
        have h1 : m j - m j' ≤ -1 := by omega
        have h2 : (N : ℤ) * (m j - m j') ≤ (N : ℤ) * (-1) :=
          mul_le_mul_of_nonneg_left h1 hNZ.le
        linarith
      · rw [h, sub_self, mul_zero] at key
        omega
      · exfalso
        have h1 : 1 ≤ m j - m j' := by omega
        have h2 : (N : ℤ) * 1 ≤ (N : ℤ) * (m j - m j') :=
          mul_le_mul_of_nonneg_left h1 hNZ.le
        linarith
    have hpos : ∀ t ∈ T.image (fun j : ℤ => j - (N : ℤ) * m j),
        c ≤ (N : ℝ) * gradLift N X t ∧ (N : ℝ) * gradLift N X t < c + 1 := by
      intro t ht
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht
      have hl := gradLift_add_mul N X j (-(m j))
      have e : j - (N : ℤ) * m j = j + (N : ℤ) * (-(m j)) := by ring
      rw [e, hl]
      have e3 : (N : ℝ) * (gradLift N X j + ((-(m j) : ℤ) : ℝ))
          = (N : ℝ) * gradLift N X j - (N : ℝ) * (m j : ℝ) := by
        push_cast
        ring
      rw [e3]
      have hh := hm j hj
      constructor <;> linarith [hh.1, hh.2]
    have hne' : (T.image (fun j : ℤ => j - (N : ℤ) * m j)).Nonempty := hne.image _
    have hcardT : ((T.image (fun j : ℤ => j - (N : ℤ) * m j)).card : ℝ) = (T.card : ℝ) := by
      rw [Finset.card_image_of_injOn hinj]
    have hsep : ∀ a ∈ T.image (fun j : ℤ => j - (N : ℤ) * m j),
        ∀ b ∈ T.image (fun j : ℤ => j - (N : ℤ) * m j), a ≤ b →
          ((N : ℝ) * ℓ) ^ (-ε) * ((b - a : ℤ) : ℝ) ≤
            (N : ℝ) * gradLift N X b - (N : ℝ) * gradLift N X a := by
      intro a _ b _ hab
      have h := (gradScaled_chain (ε := ε) (ℓ := ℓ) (N := N) (X := X) hab
        (fun l _ _ => gradEdge_full hP hX l)).1
      rwa [mul_sub] at h
    have hdiam : ∀ a ∈ T.image (fun j : ℤ => j - (N : ℤ) * m j),
        ∀ b ∈ T.image (fun j : ℤ => j - (N : ℤ) * m j),
          (N : ℝ) * gradLift N X b - (N : ℝ) * gradLift N X a < 1 := by
      intro a ha b hb
      linarith [(hpos a ha).1, (hpos a ha).2, (hpos b hb).1, (hpos b hb).2]
    have hgap := card_lt_of_gap _ hne' (fun t => (N : ℝ) * gradLift N X t)
      (((N : ℝ) * ℓ) ^ (-ε)) hδ hsep hdiam
    rw [hinv, hcardT] at hgap
    linarith

end

end Riesz1
end
