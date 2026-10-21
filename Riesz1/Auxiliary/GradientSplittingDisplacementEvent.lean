/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingWindowDefs
public import Riesz1.Auxiliary.GradientSplittingConvolutionParticle

/-!
# The displacement field: definitions, path facts and event bounds

The displacement part of Lemma 5.7. This module
contains the definitions of `V^{(1)}`, the identities relating them, and the bounds on the lift
separation `r_{ij}` on `𝒜_{ε,γ}`: `K^{-ε}|k_{ij}| ≤ N|r_{ij}| ≤ K^{ε}|k_{ij}|` and
`|N r_{ij} - k_{ij}| ≤ K^{ε}|k_{ij}|^{s/2}`, with `|k_{ij}| = d(i,j)`.
-/

@[expose] public section

open scoped ContDiff

namespace Riesz1

noncomputable section

/-! ## Definitions -/

/-- The background part of `V_i` (the two principal values), which `V^{(2)}` keeps
unchanged. -/
def gradVbg (s : ℝ) (ψ : ℝ → ℝ) (N : ℕ+) (ℓ γ : ℝ) (X : Fin (N : ℕ) → ℝ) (i : ℤ) : ℝ :=
  -2 * (N : ℝ) ^ (1 - s) * gradPV N ℓ γ (gradLift N X i)
      (fun y => gradZx ψ ℓ (gradLift N X i) y * gradKernelH s (y - gradLift N X i))
    + 2 * (N : ℝ) ^ (1 - s) * gradPV N ℓ γ (gradLift N X i)
      (fun y => gradZ ψ ℓ (gradLift N X i) y * deriv (gradKernelH s) (y - gradLift N X i))

/-- The discrete part of `V_i`: the two sums over `j ≠ i` with the path lift
`x_i + r_{ij}` and the increment `k_{ij}/N`. -/
def gradVdisc (s : ℝ) (ψ : ℝ → ℝ) (N : ℕ+) (ℓ γ : ℝ) (X : Fin (N : ℕ) → ℝ) (i : ℤ) : ℝ :=
  2 * (N : ℝ) ^ (-s) * ∑ j ∈ (gradLabels N ℓ γ).erase i,
      gradZx ψ ℓ (gradLift N X i) (gradLift N X i + gradSep N ℓ γ X i j) *
        gradKernelH s (gradSep N ℓ γ X i j)
    - 2 * (N : ℝ) ^ (-s) * ∑ j ∈ (gradLabels N ℓ γ).erase i,
      gradZ ψ ℓ (gradLift N X i) (gradLift N X i + gradSep N ℓ γ X i j) *
        deriv (gradKernelH s) ((gradPathIncr N ℓ γ i j : ℝ) / N)

/-- The reference field `V^{(2)}_i`, without its background part: the discrete
terms with `x_j` and `r_{ij}` replaced by `z_{ij} = x_i + k_{ij}/N` and `k_{ij}/N`. -/
def gradVdisc2 (s : ℝ) (ψ : ℝ → ℝ) (N : ℕ+) (ℓ γ : ℝ) (X : Fin (N : ℕ) → ℝ) (i : ℤ) : ℝ :=
  2 * (N : ℝ) ^ (-s) * ∑ j ∈ (gradLabels N ℓ γ).erase i,
      gradZx ψ ℓ (gradLift N X i) (gradLift N X i + (gradPathIncr N ℓ γ i j : ℝ) / N) *
        gradKernelH s ((gradPathIncr N ℓ γ i j : ℝ) / N)
    - 2 * (N : ℝ) ^ (-s) * ∑ j ∈ (gradLabels N ℓ γ).erase i,
      gradZ ψ ℓ (gradLift N X i) (gradLift N X i + (gradPathIncr N ℓ γ i j : ℝ) / N) *
        deriv (gradKernelH s) ((gradPathIncr N ℓ γ i j : ℝ) / N)

/-- The displacement field `V^{(1)}_i = V_i - V^{(2)}_i`, where `V^{(2)}_i` is
`gradVdisc2` plus the background part `gradVbg` of `V_i`. -/
def gradV1lab (s : ℝ) (ψ : ℝ → ℝ) (N : ℕ+) (ℓ γ : ℝ) (X : Fin (N : ℕ) → ℝ) (i : ℤ) : ℝ :=
  gradVlab s ψ N ℓ γ X i - (gradVdisc2 s ψ N ℓ γ X i + gradVbg s ψ N ℓ γ X i)

/-- `V_i` is its discrete part plus its background part. -/
lemma gradVlab_eq (s : ℝ) (ψ : ℝ → ℝ) (N : ℕ+) (ℓ γ : ℝ) (X : Fin (N : ℕ) → ℝ) (i : ℤ) :
    gradVlab s ψ N ℓ γ X i = gradVdisc s ψ N ℓ γ X i + gradVbg s ψ N ℓ γ X i := by
  unfold gradVlab gradVdisc gradVbg
  ring

/-- The displacement field is the difference of the discrete parts. -/
lemma gradV1lab_eq (s : ℝ) (ψ : ℝ → ℝ) (N : ℕ+) (ℓ γ : ℝ) (X : Fin (N : ℕ) → ℝ) (i : ℤ) :
    gradV1lab s ψ N ℓ γ X i = gradVdisc s ψ N ℓ γ X i - gradVdisc2 s ψ N ℓ γ X i := by
  unfold gradV1lab
  rw [gradVlab_eq]
  ring

/-! ## Residues and path increments -/

/-- The residue of `t` modulo `N` in the window `|t| < N`: either `t ≥ 0` and `t % N = t`, or
`t < 0` and `t % N = t + N`. -/
lemma emod_cases_of_abs_lt {t N : ℤ} (_hN : 0 < N) (h : |t| < N) :
    (0 ≤ t ∧ t % N = t) ∨ (t < 0 ∧ t % N = t + N) := by
  rcases lt_or_ge t 0 with ht | ht
  · right
    refine ⟨ht, ?_⟩
    have hgt : -N < t := by linarith [neg_abs_le t]
    have h1 : (t + N * 1) % N = t % N := Int.add_mul_emod_self_left t N 1
    rw [← h1, mul_one]
    exact Int.emod_eq_of_lt (by linarith) (by linarith)
  · left
    refine ⟨ht, ?_⟩
    exact Int.emod_eq_of_lt ht (by linarith [le_abs_self t])

/-- On the window the label difference has `2|j - i| ≤ N` when both labels are in the partial
window. -/
lemma gradLabels_partial_two_abs_le {ℓ γ : ℝ} {N : ℕ+} (hP : GradPartial N ℓ γ) {i j : ℤ}
    (hi : i ∈ gradLabels N ℓ γ) (hj : j ∈ gradLabels N ℓ γ) : 2 * |j - i| ≤ ((N : ℕ) : ℤ) := by
  rw [mem_gradLabels_partial hP] at hi hj
  have hPN : gradM N ℓ γ < (N : ℝ) / 8 := hP
  have hM : ((⌊gradM N ℓ γ⌋ : ℤ) : ℝ) ≤ gradM N ℓ γ := Int.floor_le _
  have h8 : 8 * ⌊gradM N ℓ γ⌋ < ((N : ℕ) : ℤ) := by
    have h2 : (8 * (⌊gradM N ℓ γ⌋ : ℝ)) < ((N : ℕ) : ℝ) := by linarith
    exact_mod_cast h2
  have hab : |j - i| ≤ 2 * ⌊gradM N ℓ γ⌋ := by
    rw [abs_le]
    constructor <;> omega
  omega

/-- The increment of the chosen path has absolute value `d(i,j)`. -/
lemma abs_gradPathIncr_eq {ℓ γ : ℝ} {N : ℕ+} {i j : ℤ} (hi : i ∈ gradLabels N ℓ γ)
    (hj : j ∈ gradLabels N ℓ γ) :
    |(gradPathIncr N ℓ γ i j : ℤ)| = gradLabelDist N i j := by
  have hNpos : (0 : ℤ) < ((N : ℕ) : ℤ) := by exact_mod_cast N.pos
  have hlt := gradLabels_abs_sub_lt hi hj
  unfold gradPathIncr gradLabelDist
  by_cases hP : GradPartial N ℓ γ
  · simp only [hP, ↓reduceIte]
    have h2 := gradLabels_partial_two_abs_le hP hi hj
    rw [min_eq_left (by linarith)]
  · simp only [hP, ↓reduceIte]
    have hlo : -((N : ℕ) : ℤ) < j - i := (abs_lt.mp hlt).1
    have hhi : j - i < ((N : ℕ) : ℤ) := (abs_lt.mp hlt).2
    rcases emod_cases_of_abs_lt hNpos hlt with ⟨ht, hr⟩ | ⟨ht, hr⟩
    · rw [hr, abs_of_nonneg ht]
      simp only [abs_eq_max_neg, max_def, min_def]
      repeat' split_ifs
      all_goals omega
    · rw [hr, abs_of_neg ht]
      simp only [abs_eq_max_neg, max_def, min_def]
      repeat' split_ifs
      all_goals omega

/-- The label distance is at most half the window: `2 d(i,j) ≤ N`. -/
lemma two_gradLabelDist_le (N : ℕ+) (i j : ℤ) : 2 * gradLabelDist N i j ≤ ((N : ℕ) : ℤ) := by
  unfold gradLabelDist
  omega

/-- The path increment has `2|k_{ij}| ≤ N` on the window. -/
lemma two_abs_gradPathIncr_le {ℓ γ : ℝ} {N : ℕ+} {i j : ℤ} (hi : i ∈ gradLabels N ℓ γ)
    (hj : j ∈ gradLabels N ℓ γ) : 2 * |(gradPathIncr N ℓ γ i j : ℤ)| ≤ ((N : ℕ) : ℤ) := by
  rw [abs_gradPathIncr_eq hi hj]
  exact two_gradLabelDist_le N i j

/-- The path increment is nonzero when `j ≠ i`. -/
lemma gradPathIncr_ne_zero {ℓ γ : ℝ} {N : ℕ+} {i j : ℤ} (hi : i ∈ gradLabels N ℓ γ)
    (hj : j ∈ gradLabels N ℓ γ) (hne : j ≠ i) : gradPathIncr N ℓ γ i j ≠ 0 := by
  intro h0
  have h := abs_gradPathIncr_eq hi hj
  rw [h0, abs_zero] at h
  have hlt := gradLabels_abs_sub_lt hi hj
  have hpos : (0 : ℤ) < |j - i| := abs_pos.mpr (sub_ne_zero.mpr hne)
  unfold gradLabelDist at h
  omega

/-- The chain of edges on a full window, between arbitrary integer labels `a ≤ b`. -/
lemma gradChain_full {s γ ε ℓ : ℝ} {N : ℕ+} {X : Fin (N : ℕ) → ℝ} (hP : ¬GradPartial N ℓ γ)
    (hX : gradEvent s γ ε N ℓ X) {a b : ℤ} (hab : a ≤ b) :
    ((N : ℝ) * ℓ) ^ (-ε) * ((b - a : ℤ) : ℝ) ≤ (N : ℝ) * (gradLift N X b - gradLift N X a) ∧
      (N : ℝ) * (gradLift N X b - gradLift N X a) ≤ ((N : ℝ) * ℓ) ^ ε * ((b - a : ℤ) : ℝ) :=
  gradScaled_chain hab (fun l _ _ => gradEdge_full hP hX l)

/-- The chain of edges on a partial window, between labels `a ≤ b` of the window. -/
lemma gradChain_partial {s γ ε ℓ : ℝ} {N : ℕ+} {X : Fin (N : ℕ) → ℝ} (hP : GradPartial N ℓ γ)
    (hX : gradEvent s γ ε N ℓ X) {a b : ℤ} (hab : a ≤ b) (ha : a ∈ gradLabels N ℓ γ)
    (hb : b ∈ gradLabels N ℓ γ) :
    ((N : ℝ) * ℓ) ^ (-ε) * ((b - a : ℤ) : ℝ) ≤ (N : ℝ) * (gradLift N X b - gradLift N X a) ∧
      (N : ℝ) * (gradLift N X b - gradLift N X a) ≤ ((N : ℝ) * ℓ) ^ ε * ((b - a : ℤ) : ℝ) :=
  gradEdge_partial_chain hX hab ha hb hP

/-- Real algebra of the spacing bounds, positive increment: if `μ k ≤ N D ≤ λ k` with `k > 0`,
then `N |D|` lies in `[μ |k|, λ |k|]` and `D` has the sign of `k`. -/
lemma sep_bounds_of_pos {N μ up k D : ℝ} (hN : 0 < N) (hμ : 0 < μ) (hk : 0 < k)
    (h1 : μ * k ≤ N * D) (h2 : N * D ≤ up * k) :
    μ * |k| ≤ N * |D| ∧ N * |D| ≤ up * |k| ∧ 0 < D * k := by
  have hD : 0 < D := by
    by_contra hcon
    push Not at hcon
    nlinarith [mul_pos hμ hk]
  rw [abs_of_pos hk, abs_of_pos hD]
  exact ⟨h1, h2, mul_pos hD hk⟩

/-- Real algebra of the spacing bounds, negative increment: if `μ (-k) ≤ N E ≤ λ (-k)` with
`k < 0`, then `N |-E|` lies in `[μ |k|, λ |k|]` and `(-E)` has the sign of `k`. -/
lemma sep_bounds_of_neg {N μ up k E : ℝ} (hN : 0 < N) (hμ : 0 < μ) (hk : k < 0)
    (h1 : μ * (-k) ≤ N * E) (h2 : N * E ≤ up * (-k)) :
    μ * |k| ≤ N * |-E| ∧ N * |-E| ≤ up * |k| ∧ 0 < -E * k := by
  have hE : 0 < E := by
    by_contra hcon
    push Not at hcon
    nlinarith [mul_pos hμ (neg_pos.mpr hk)]
  rw [abs_of_neg hk, abs_neg, abs_of_pos hE]
  refine ⟨by linarith, by linarith, mul_pos_of_neg_of_neg (by linarith) hk⟩

/-- The lift separation `r_{ij}` has `K^{-ε}|k_{ij}| ≤ N|r_{ij}| ≤ K^{ε}|k_{ij}|` and the sign of
`k_{ij}` on `𝒜_{ε,γ}` (displacement part of Lemma 5.7, the spacing bounds of the
path). -/
lemma gradSep_abs_bounds {s γ ε ℓ : ℝ} {N : ℕ+} {X : Fin (N : ℕ) → ℝ}
    (hK : 1 ≤ ((N : ℕ) : ℝ) * ℓ) (hX : gradEvent s γ ε N ℓ X) {i j : ℤ}
    (hi : i ∈ gradLabels N ℓ γ) (hj : j ∈ gradLabels N ℓ γ) (hne : j ≠ i) :
    ((N : ℝ) * ℓ) ^ (-ε) * |(gradPathIncr N ℓ γ i j : ℝ)|
        ≤ (N : ℝ) * |gradSep N ℓ γ X i j| ∧
      (N : ℝ) * |gradSep N ℓ γ X i j| ≤ ((N : ℝ) * ℓ) ^ ε * |(gradPathIncr N ℓ γ i j : ℝ)| ∧
      0 < gradSep N ℓ γ X i j * (gradPathIncr N ℓ γ i j : ℝ) := by
  have hk0 := gradPathIncr_ne_zero hi hj hne
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast N.pos
  have hK0 : 0 < (N : ℝ) * ℓ := by
    have hN1 : (0 : ℝ) < (N : ℝ) := hN0
    linarith
  have hμ : 0 < ((N : ℝ) * ℓ) ^ (-ε) := Real.rpow_pos_of_pos hK0 _
  have hsep : gradSep N ℓ γ X i j
      = gradLift N X (i + gradPathIncr N ℓ γ i j) - gradLift N X i := rfl
  rw [hsep]
  by_cases hP : GradPartial N ℓ γ
  · have hik : i + gradPathIncr N ℓ γ i j = j := by
      unfold gradPathIncr
      simp only [hP, ↓reduceIte]
      ring
    rcases lt_or_gt_of_ne hk0 with hneg | hpos
    · have hc := gradChain_partial hP hX (a := i + gradPathIncr N ℓ γ i j) (b := i)
        (by omega) (by rw [hik]; exact hj) hi
      have e : ((i - (i + gradPathIncr N ℓ γ i j) : ℤ) : ℝ)
          = -((gradPathIncr N ℓ γ i j : ℤ) : ℝ) := by
        push_cast
        ring
      rw [e] at hc
      have hkR : ((gradPathIncr N ℓ γ i j : ℤ) : ℝ) < 0 := by exact_mod_cast hneg
      obtain ⟨c1, c2, c3⟩ := sep_bounds_of_neg hN0 hμ hkR hc.1 hc.2
      rw [show -(gradLift N X i - gradLift N X (i + gradPathIncr N ℓ γ i j))
          = gradLift N X (i + gradPathIncr N ℓ γ i j) - gradLift N X i by ring] at c1 c2 c3
      exact ⟨c1, c2, c3⟩
    · have hc := gradChain_partial hP hX (a := i) (b := i + gradPathIncr N ℓ γ i j)
        (by omega) hi (by rw [hik]; exact hj)
      have e : ((i + gradPathIncr N ℓ γ i j - i : ℤ) : ℝ)
          = ((gradPathIncr N ℓ γ i j : ℤ) : ℝ) := by
        push_cast
        ring
      rw [e] at hc
      have hkR : 0 < ((gradPathIncr N ℓ γ i j : ℤ) : ℝ) := by exact_mod_cast hpos
      exact sep_bounds_of_pos hN0 hμ hkR hc.1 hc.2
  · rcases lt_or_gt_of_ne hk0 with hneg | hpos
    · have hc := gradChain_full hP hX (a := i + gradPathIncr N ℓ γ i j) (b := i) (by omega)
      have e : ((i - (i + gradPathIncr N ℓ γ i j) : ℤ) : ℝ)
          = -((gradPathIncr N ℓ γ i j : ℤ) : ℝ) := by
        push_cast
        ring
      rw [e] at hc
      have hkR : ((gradPathIncr N ℓ γ i j : ℤ) : ℝ) < 0 := by exact_mod_cast hneg
      obtain ⟨c1, c2, c3⟩ := sep_bounds_of_neg hN0 hμ hkR hc.1 hc.2
      rw [show -(gradLift N X i - gradLift N X (i + gradPathIncr N ℓ γ i j))
          = gradLift N X (i + gradPathIncr N ℓ γ i j) - gradLift N X i by ring] at c1 c2 c3
      exact ⟨c1, c2, c3⟩
    · have hc := gradChain_full hP hX (a := i) (b := i + gradPathIncr N ℓ γ i j) (by omega)
      have e : ((i + gradPathIncr N ℓ γ i j - i : ℤ) : ℝ)
          = ((gradPathIncr N ℓ γ i j : ℤ) : ℝ) := by
        push_cast
        ring
      rw [e] at hc
      have hkR : 0 < ((gradPathIncr N ℓ γ i j : ℤ) : ℝ) := by exact_mod_cast hpos
      exact sep_bounds_of_pos hN0 hμ hkR hc.1 hc.2

/-- The event's first inequality for the lift separation:
`|N r_{ij} - k_{ij}| ≤ K^ε |k_{ij}|^{s/2}` (data part of Lemma 5.7). -/
lemma gradSep_event_bound {s γ ε ℓ : ℝ} {N : ℕ+} {X : Fin (N : ℕ) → ℝ}
    (hX : gradEvent s γ ε N ℓ X) {i j : ℤ} (hi : i ∈ gradLabels N ℓ γ)
    (hj : j ∈ gradLabels N ℓ γ) (hne : j ≠ i) :
    |(N : ℝ) * gradSep N ℓ γ X i j - (gradPathIncr N ℓ γ i j : ℝ)|
      ≤ ((N : ℝ) * ℓ) ^ ε * |(gradPathIncr N ℓ γ i j : ℝ)| ^ (s / 2) := by
  have hk0 := gradPathIncr_ne_zero hi hj hne
  have h2 := two_abs_gradPathIncr_le hi hj
  have hin : gradInWindow N ℓ γ (i + gradPathIncr N ℓ γ i j) := by
    by_cases hP : GradPartial N ℓ γ
    · intro _
      have hik : i + gradPathIncr N ℓ γ i j = j := by
        unfold gradPathIncr
        simp only [hP, ↓reduceIte]
        ring
      rw [hik]
      exact hj
    · intro hPart
      exact absurd hPart hP
  exact hX.1 i hi (gradPathIncr N ℓ γ i j) hin hk0 h2

/-- On a partial window, `4|k_{ij}| ≤ N`. -/
lemma four_abs_gradPathIncr_partial {ℓ γ : ℝ} {N : ℕ+} {i j : ℤ} (hP : GradPartial N ℓ γ)
    (hi : i ∈ gradLabels N ℓ γ) (hj : j ∈ gradLabels N ℓ γ) :
    4 * |(gradPathIncr N ℓ γ i j : ℤ)| ≤ ((N : ℕ) : ℤ) := by
  unfold gradPathIncr
  simp only [hP, ↓reduceIte]
  rw [mem_gradLabels_partial hP] at hi hj
  have hPN : gradM N ℓ γ < (N : ℝ) / 8 := hP
  have hM : ((⌊gradM N ℓ γ⌋ : ℤ) : ℝ) ≤ gradM N ℓ γ := Int.floor_le _
  have h8 : 8 * ⌊gradM N ℓ γ⌋ < ((N : ℕ) : ℤ) := by
    have h2 : (8 * (⌊gradM N ℓ γ⌋ : ℝ)) < ((N : ℕ) : ℝ) := by linarith
    exact_mod_cast h2
  have hab : |j - i| ≤ 2 * ⌊gradM N ℓ γ⌋ := by
    rw [abs_le]
    constructor <;> omega
  omega

/-- On a full window with `2 ≤ N`, `K ≥ 1` and `K^ε ≤ 2`, the lift separation satisfies
`|r_{ij}| ≤ 3/4`. On a partial window `N|r| ≤ K^ε |k| ≤ 2 |k| ≤ N/2`. On a full window the
complementary edge chain keeps `r` at distance at least `K^{-ε}/2` from the integers. -/
lemma gradSep_abs_le_three_quarters {s γ ε ℓ : ℝ} {N : ℕ+} {X : Fin (N : ℕ) → ℝ}
    (hK : 1 ≤ ((N : ℕ) : ℝ) * ℓ) (hlam : (((N : ℕ) : ℝ) * ℓ) ^ ε ≤ 2)
    (hX : gradEvent s γ ε N ℓ X) {i j : ℤ} (hi : i ∈ gradLabels N ℓ γ)
    (hj : j ∈ gradLabels N ℓ γ) (hne : j ≠ i) :
    |gradSep N ℓ γ X i j| ≤ 3 / 4 := by
  have hN0 : (0 : ℝ) < ((N : ℕ) : ℝ) := by exact_mod_cast N.pos
  have hK0 : 0 < ((N : ℕ) : ℝ) * ℓ := by linarith
  have hlampos : 0 < (((N : ℕ) : ℝ) * ℓ) ^ ε := Real.rpow_pos_of_pos hK0 _
  have hμ0 : (0 : ℝ) ≤ (((N : ℕ) : ℝ) * ℓ) ^ (-ε) := Real.rpow_nonneg hK0.le _
  have hμhalf : (1 / 2 : ℝ) ≤ (((N : ℕ) : ℝ) * ℓ) ^ (-ε) := by
    rw [Real.rpow_neg hK0.le]
    calc (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
      _ ≤ ((((N : ℕ) : ℝ) * ℓ) ^ ε)⁻¹ := inv_anti₀ hlampos hlam
  obtain ⟨b1, b2, b3⟩ := gradSep_abs_bounds hK hX hi hj hne
  have hk0 := gradPathIncr_ne_zero hi hj hne
  have hκR : (gradPathIncr N ℓ γ i j : ℝ) ≠ 0 := by exact_mod_cast hk0
  by_cases hP : GradPartial N ℓ γ
  · -- partial window: `N|r| ≤ 2|k| ≤ N/2`
    have h4 := four_abs_gradPathIncr_partial hP hi hj
    have h4R : 4 * |((gradPathIncr N ℓ γ i j : ℤ) : ℝ)| ≤ ((N : ℕ) : ℝ) := by
      rw [← Int.cast_abs]
      exact_mod_cast h4
    have hA : (((N : ℕ) : ℝ) * ℓ) ^ ε * |((gradPathIncr N ℓ γ i j : ℤ) : ℝ)| ≤ 2 * |((gradPathIncr N ℓ γ i j : ℤ) : ℝ)| :=
      mul_le_mul_of_nonneg_right hlam (abs_nonneg _)
    have hB : ((N : ℕ) : ℝ) * |gradSep N ℓ γ X i j| ≤ ((N : ℕ) : ℝ) * (1 / 2) := by
      nlinarith [abs_nonneg ((gradPathIncr N ℓ γ i j : ℤ) : ℝ)]
    have hC := le_of_mul_le_mul_left hB hN0
    linarith
  · -- full window: the two complementary chains
    have h2 := two_abs_gradPathIncr_le hi hj
    have hμ1 := hμhalf
    rcases lt_or_gt_of_ne hk0 with hneg | hpos
    · have hκN : (((N : ℕ) : ℤ) + (gradPathIncr N ℓ γ i j : ℤ)) > 0 := by
        rw [abs_of_neg hneg] at h2
        omega
      have hc := gradChain_full hP hX (a := i) (b := i + (((N : ℕ) : ℤ) + gradPathIncr N ℓ γ i j))
        (by omega)
      have hlift : gradLift N X (i + (((N : ℕ) : ℤ) + gradPathIncr N ℓ γ i j))
          = gradLift N X (i + gradPathIncr N ℓ γ i j) + 1 := by
        have := gradLift_add_mul N X (i + gradPathIncr N ℓ γ i j) 1
        rw [mul_one] at this
        rw [show i + (((N : ℕ) : ℤ) + gradPathIncr N ℓ γ i j)
            = i + gradPathIncr N ℓ γ i j + ((N : ℕ) : ℤ) by ring]
        simpa using this
      have ecast : ((i + (((N : ℕ) : ℤ) + gradPathIncr N ℓ γ i j) - i : ℤ) : ℝ)
          = ((N : ℕ) : ℝ) + ((gradPathIncr N ℓ γ i j : ℤ) : ℝ) := by
        push_cast
        ring
      rw [ecast, hlift] at hc
      have hκR' : ((gradPathIncr N ℓ γ i j : ℤ) : ℝ) < 0 := by exact_mod_cast hneg
      have h2R : 2 * ((gradPathIncr N ℓ γ i j : ℤ) : ℝ) ≥ -((N : ℕ) : ℝ) := by
        have : (2 : ℝ) * |((gradPathIncr N ℓ γ i j : ℤ) : ℝ)| ≤ ((N : ℕ) : ℝ) := by
          rw [← Int.cast_abs]
          exact_mod_cast h2
        rw [abs_of_neg hκR'] at this
        linarith
      have hD : gradSep N ℓ γ X i j
          = gradLift N X (i + gradPathIncr N ℓ γ i j) - gradLift N X i := rfl
      rw [hD] at b3 ⊢
      have hDneg : gradLift N X (i + gradPathIncr N ℓ γ i j) - gradLift N X i < 0 := by
        by_contra hcon
        push Not at hcon
        nlinarith [b3, hcon]
      rw [abs_of_neg hDneg]
      have hμN : (1 / 2 : ℝ) * ((N : ℕ) : ℝ) ≤ (((N : ℕ) : ℝ) * ℓ) ^ (-ε) * ((N : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hμhalf hN0.le
      have hA : (((N : ℕ) : ℝ) * ℓ) ^ (-ε) * (((N : ℕ) : ℝ) / 2)
          ≤ (((N : ℕ) : ℝ) * ℓ) ^ (-ε) * (((N : ℕ) : ℝ) + (gradPathIncr N ℓ γ i j : ℤ)) :=
        mul_le_mul_of_nonneg_left (by linarith) hμ0
      have hND : ((N : ℕ) : ℝ) * (-(gradLift N X (i + gradPathIncr N ℓ γ i j) - gradLift N X i))
          ≤ ((N : ℕ) : ℝ) * (3 / 4) := by
        nlinarith [hc.1, hA, hμN]
      exact le_of_mul_le_mul_left hND hN0
    · have hκN : ((N : ℕ) : ℤ) - (gradPathIncr N ℓ γ i j : ℤ) > 0 := by
        rw [abs_of_pos hpos] at h2
        omega
      have hc := gradChain_full hP hX (a := i + gradPathIncr N ℓ γ i j) (b := i + ((N : ℕ) : ℤ))
        (by omega)
      have hlift : gradLift N X (i + ((N : ℕ) : ℤ)) = gradLift N X i + 1 := by
        have := gradLift_add_mul N X i 1
        rw [mul_one] at this
        simpa using this
      have ecast : ((i + ((N : ℕ) : ℤ) - (i + gradPathIncr N ℓ γ i j) : ℤ) : ℝ)
          = ((N : ℕ) : ℝ) - ((gradPathIncr N ℓ γ i j : ℤ) : ℝ) := by
        push_cast
        ring
      rw [ecast, hlift] at hc
      have hkR : 0 < ((gradPathIncr N ℓ γ i j : ℤ) : ℝ) := by exact_mod_cast hpos
      have hκhalf : 2 * ((gradPathIncr N ℓ γ i j : ℤ) : ℝ) ≤ ((N : ℕ) : ℝ) := by
        have : (2 : ℝ) * |((gradPathIncr N ℓ γ i j : ℤ) : ℝ)| ≤ ((N : ℕ) : ℝ) := by
          rw [← Int.cast_abs]
          exact_mod_cast h2
        rwa [abs_of_pos hkR] at this
      have hD : gradSep N ℓ γ X i j
          = gradLift N X (i + gradPathIncr N ℓ γ i j) - gradLift N X i := rfl
      rw [hD] at b3 ⊢
      have hDpos : 0 < gradLift N X (i + gradPathIncr N ℓ γ i j) - gradLift N X i :=
        (mul_pos_iff_of_pos_right hkR).mp b3
      rw [abs_of_pos hDpos]
      have hμN : (1 / 2 : ℝ) * ((N : ℕ) : ℝ) ≤ (((N : ℕ) : ℝ) * ℓ) ^ (-ε) * ((N : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hμhalf hN0.le
      have hA : (((N : ℕ) : ℝ) * ℓ) ^ (-ε) * (((N : ℕ) : ℝ) / 2)
          ≤ (((N : ℕ) : ℝ) * ℓ) ^ (-ε) * (((N : ℕ) : ℝ) - (gradPathIncr N ℓ γ i j : ℤ)) :=
        mul_le_mul_of_nonneg_left (by linarith) hμ0
      have hND : ((N : ℕ) : ℝ) * (gradLift N X (i + gradPathIncr N ℓ γ i j) - gradLift N X i)
          ≤ ((N : ℕ) : ℝ) * (3 / 4) := by
        nlinarith [hc.1, hA, hμN]
      exact le_of_mul_le_mul_left hND hN0

end

end Riesz1
