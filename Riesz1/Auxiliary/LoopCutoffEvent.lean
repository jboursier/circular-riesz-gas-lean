/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopCutoffDefs
public import Riesz1.Rigidity.Gaps

/-!
# The anchored cutoff: values and the good event

The cutoff part of Lemma 5.8, the deterministic clause: on the ordered domain, the
event `η > 0` implies the good event `𝒜_{ε,2γ}` (`gradEvent s (2 * γ) ε N ℓ`).

The cutoff `η` takes values in `[0, 1]` everywhere. Its factors are each one unless one of their
arguments exceeds one. The contrapositive of this fact is the basis of the probability bound in
`LoopCutoffProbability.lean`.
-/

@[expose] public section

open Finset

namespace Riesz1

noncomputable section

variable {N : ℕ+}

/-- The cyclic lift of a configuration is the gradient-splitting lift of its underlying point. -/
lemma gradLift_val (X : Configuration N) (j : ℤ) :
    gradLift N X.val j = cyclicLift X j := rfl

/-- A factor of the form `if p then c(r) else 1` lies in `[0, 1]`. -/
lemma ite_cutoff_mem_Icc (p : Prop) [Decidable p] (r : ℝ) :
    0 ≤ (if p then cutoffC r else 1) ∧ (if p then cutoffC r else 1) ≤ 1 := by
  split_ifs
  · exact cutoffC_mem_Icc r
  · exact ⟨zero_le_one, le_rfl⟩

/-- Each factor of a product of nonnegative terms is positive when the product is positive. -/
lemma pos_factor_of_prod_pos {ι : Type*} {S : Finset ι} {f : ι → ℝ}
    (hnn : ∀ i ∈ S, 0 ≤ f i) (h : 0 < ∏ i ∈ S, f i) {i : ι} (hi : i ∈ S) : 0 < f i := by
  rcases (hnn i hi).lt_or_eq with h1 | h1
  · exact h1
  · exact absurd (Finset.prod_eq_zero hi h1.symm) h.ne'

/-- If two nonnegative reals have positive product, both are positive. -/
lemma pos_pos_of_mul_pos {A B : ℝ} (hA : 0 ≤ A) (h : 0 < A * B) :
    0 < A ∧ 0 < B := by
  rcases mul_pos_iff.mp h with ⟨h1, h2⟩ | ⟨h1, _⟩
  · exact ⟨h1, h2⟩
  · exact absurd h1 (not_lt.mpr hA)

/-- The anchored cutoff takes values in `[0, 1]` at every point. -/
lemma loopCutoff_mem_Icc (s γ ε : ℝ) (ℓ : ℝ) (X : Fin (N : ℕ) → ℝ) :
    0 ≤ loopCutoff s γ ε N ℓ X ∧ loopCutoff s γ ε N ℓ X ≤ 1 := by
  unfold loopCutoff
  have hA : ∀ i ∈ gradLabels N ℓ (2 * γ), 0 ≤
      ∏ k ∈ Finset.Icc (-((N : ℤ) / 2)) ((N : ℤ) / 2),
        (if k ≠ 0 ∧ gradInWindow N ℓ (2 * γ) (i + k) then
          cutoffC (2 * |(N : ℝ) * (gradLift N X (i + k) - gradLift N X i) - k| /
            (((N : ℝ) * ℓ) ^ ε * |(k : ℝ)| ^ (s / 2))) else 1) :=
    fun i _ => Finset.prod_nonneg fun k _ => (ite_cutoff_mem_Icc _ _).1
  have hA1 : ∀ i ∈ gradLabels N ℓ (2 * γ),
      ∏ k ∈ Finset.Icc (-((N : ℤ) / 2)) ((N : ℤ) / 2),
        (if k ≠ 0 ∧ gradInWindow N ℓ (2 * γ) (i + k) then
          cutoffC (2 * |(N : ℝ) * (gradLift N X (i + k) - gradLift N X i) - k| /
            (((N : ℝ) * ℓ) ^ ε * |(k : ℝ)| ^ (s / 2))) else 1) ≤ 1 :=
    fun i _ => Finset.prod_le_one₀ (fun k _ => (ite_cutoff_mem_Icc _ _).1)
      (fun k _ => (ite_cutoff_mem_Icc _ _).2)
  have hB0 : 0 ≤ ∏ i ∈ gradLabels N ℓ (2 * γ),
      (if gradInWindow N ℓ (2 * γ) (i + 1) then
        cutoffC (2 * ((N : ℝ) * (gradLift N X (i + 1) - gradLift N X i)) / ((N : ℝ) * ℓ) ^ ε) *
          cutoffC (2 / (((N : ℝ) * ℓ) ^ ε * ((N : ℝ) * (gradLift N X (i + 1) - gradLift N X i))))
      else 1) := by
    refine Finset.prod_nonneg fun i _ => ?_
    split_ifs
    · exact mul_nonneg (cutoffC_mem_Icc _).1 (cutoffC_mem_Icc _).1
    · exact zero_le_one
  have hB1 : ∏ i ∈ gradLabels N ℓ (2 * γ),
      (if gradInWindow N ℓ (2 * γ) (i + 1) then
        cutoffC (2 * ((N : ℝ) * (gradLift N X (i + 1) - gradLift N X i)) / ((N : ℝ) * ℓ) ^ ε) *
          cutoffC (2 / (((N : ℝ) * ℓ) ^ ε * ((N : ℝ) * (gradLift N X (i + 1) - gradLift N X i))))
      else 1) ≤ 1 := by
    refine Finset.prod_le_one₀ (fun i _ => ?_) (fun i _ => ?_)
    · split_ifs
      · exact mul_nonneg (cutoffC_mem_Icc _).1 (cutoffC_mem_Icc _).1
      · exact zero_le_one
    · split_ifs
      · calc _ ≤ 1 * 1 := mul_le_mul (cutoffC_mem_Icc _).2 (cutoffC_mem_Icc _).2 (cutoffC_mem_Icc _).1 zero_le_one
          _ = 1 := one_mul 1
      · exact le_rfl
  have hA0 : 0 ≤ ∏ i ∈ gradLabels N ℓ (2 * γ),
      ∏ k ∈ Finset.Icc (-((N : ℤ) / 2)) ((N : ℤ) / 2),
        (if k ≠ 0 ∧ gradInWindow N ℓ (2 * γ) (i + k) then
          cutoffC (2 * |(N : ℝ) * (gradLift N X (i + k) - gradLift N X i) - k| /
            (((N : ℝ) * ℓ) ^ ε * |(k : ℝ)| ^ (s / 2))) else 1) :=
    Finset.prod_nonneg hA
  have hA2 : ∏ i ∈ gradLabels N ℓ (2 * γ),
      ∏ k ∈ Finset.Icc (-((N : ℤ) / 2)) ((N : ℤ) / 2),
        (if k ≠ 0 ∧ gradInWindow N ℓ (2 * γ) (i + k) then
          cutoffC (2 * |(N : ℝ) * (gradLift N X (i + k) - gradLift N X i) - k| /
            (((N : ℝ) * ℓ) ^ ε * |(k : ℝ)| ^ (s / 2))) else 1) ≤ 1 :=
    Finset.prod_le_one₀ (fun i hi => hA i hi) hA1
  constructor
  · exact mul_nonneg hA0 hB0
  · calc _ ≤ 1 * 1 := mul_le_mul hA2 hB1 hB0 zero_le_one
      _ = 1 := one_mul 1

/-- If every pair argument and every edge argument of `η` is at most one, then `η = 1`. -/
lemma loopCutoff_eq_one_of_le (s γ ε : ℝ) (ℓ : ℝ) (X : Fin (N : ℕ) → ℝ)
    (hA : ∀ i ∈ gradLabels N ℓ (2 * γ), ∀ k ∈ Finset.Icc (-((N : ℤ) / 2)) ((N : ℤ) / 2),
      k ≠ 0 → gradInWindow N ℓ (2 * γ) (i + k) →
        2 * |(N : ℝ) * (gradLift N X (i + k) - gradLift N X i) - k| /
          (((N : ℝ) * ℓ) ^ ε * |(k : ℝ)| ^ (s / 2)) ≤ 1)
    (hB : ∀ i ∈ gradLabels N ℓ (2 * γ), gradInWindow N ℓ (2 * γ) (i + 1) →
      2 * ((N : ℝ) * (gradLift N X (i + 1) - gradLift N X i)) / ((N : ℝ) * ℓ) ^ ε ≤ 1 ∧
        2 / (((N : ℝ) * ℓ) ^ ε * ((N : ℝ) * (gradLift N X (i + 1) - gradLift N X i))) ≤ 1) :
    loopCutoff s γ ε N ℓ X = 1 := by
  unfold loopCutoff
  have h1 : ∏ i ∈ gradLabels N ℓ (2 * γ), ∏ k ∈ Finset.Icc (-((N : ℤ) / 2)) ((N : ℤ) / 2),
      (if k ≠ 0 ∧ gradInWindow N ℓ (2 * γ) (i + k) then
        cutoffC (2 * |(N : ℝ) * (gradLift N X (i + k) - gradLift N X i) - k| /
          (((N : ℝ) * ℓ) ^ ε * |(k : ℝ)| ^ (s / 2))) else 1) = 1 := by
    refine Finset.prod_eq_one fun i hi => Finset.prod_eq_one fun k hk => ?_
    split_ifs with hc
    · exact cutoffC_eq_one_of_le (hA i hi k hk hc.1 hc.2)
    · rfl
  have h2 : ∏ i ∈ gradLabels N ℓ (2 * γ),
      (if gradInWindow N ℓ (2 * γ) (i + 1) then
        cutoffC (2 * ((N : ℝ) * (gradLift N X (i + 1) - gradLift N X i)) / ((N : ℝ) * ℓ) ^ ε) *
          cutoffC (2 / (((N : ℝ) * ℓ) ^ ε * ((N : ℝ) * (gradLift N X (i + 1) - gradLift N X i))))
      else 1) = 1 := by
    refine Finset.prod_eq_one fun i hi => ?_
    split_ifs with hc
    · rw [cutoffC_eq_one_of_le (hB i hi hc).1, cutoffC_eq_one_of_le (hB i hi hc).2, mul_one]
    · rfl
  rw [h1, h2, one_mul]

/-- The cutoff `η` is not one only if some pair argument or some edge argument exceeds one. -/
lemma exists_gt_one_of_loopCutoff_ne_one (s γ ε : ℝ) (ℓ : ℝ) (X : Fin (N : ℕ) → ℝ)
    (h : loopCutoff s γ ε N ℓ X ≠ 1) :
    (∃ i ∈ gradLabels N ℓ (2 * γ), ∃ k ∈ Finset.Icc (-((N : ℤ) / 2)) ((N : ℤ) / 2),
      k ≠ 0 ∧ gradInWindow N ℓ (2 * γ) (i + k) ∧
        1 < 2 * |(N : ℝ) * (gradLift N X (i + k) - gradLift N X i) - k| /
          (((N : ℝ) * ℓ) ^ ε * |(k : ℝ)| ^ (s / 2))) ∨
    (∃ i ∈ gradLabels N ℓ (2 * γ), gradInWindow N ℓ (2 * γ) (i + 1) ∧
      (1 < 2 * ((N : ℝ) * (gradLift N X (i + 1) - gradLift N X i)) / ((N : ℝ) * ℓ) ^ ε ∨
        1 < 2 / (((N : ℝ) * ℓ) ^ ε * ((N : ℝ) * (gradLift N X (i + 1) - gradLift N X i))))) := by
  by_contra hcon
  apply h
  refine loopCutoff_eq_one_of_le s γ ε ℓ X (fun i hi k hk hk0 hw => ?_) (fun i hi hw => ?_)
  · by_contra hgt
    exact hcon (Or.inl ⟨i, hi, k, hk, hk0, hw, not_le.mp hgt⟩)
  · constructor
    · by_contra hgt
      exact hcon (Or.inr ⟨i, hi, hw, Or.inl (not_le.mp hgt)⟩)
    · by_contra hgt
      exact hcon (Or.inr ⟨i, hi, hw, Or.inr (not_le.mp hgt)⟩)

/-- On the ordered domain, `η > 0` forces every pair and edge argument below its threshold, which
is the good event `𝒜_{ε,2γ}`. The cutoff part of Lemma 5.8. -/
lemma gradEvent_of_loopCutoff_pos {s γ ε ℓ : ℝ} (hℓ : 0 < ℓ) (X : Configuration N)
    (h : 0 < loopCutoff s γ ε N ℓ X.val) : gradEvent s (2 * γ) ε N ℓ X.val := by
  have hK : (0 : ℝ) < (N : ℝ) * ℓ := mul_pos (by exact_mod_cast N.pos) hℓ
  have hKε : ∀ e : ℝ, 0 < ((N : ℝ) * ℓ) ^ e := fun e => Real.rpow_pos_of_pos hK e
  unfold loopCutoff at h
  have hA0 : ∀ i ∈ gradLabels N ℓ (2 * γ), 0 ≤
      ∏ k ∈ Finset.Icc (-((N : ℤ) / 2)) ((N : ℤ) / 2),
        (if k ≠ 0 ∧ gradInWindow N ℓ (2 * γ) (i + k) then
          cutoffC (2 * |(N : ℝ) * (gradLift N X.val (i + k) - gradLift N X.val i) - k| /
            (((N : ℝ) * ℓ) ^ ε * |(k : ℝ)| ^ (s / 2))) else 1) :=
    fun i _ => Finset.prod_nonneg fun k _ => (ite_cutoff_mem_Icc _ _).1
  have hB0 : ∀ i ∈ gradLabels N ℓ (2 * γ), 0 ≤
      (if gradInWindow N ℓ (2 * γ) (i + 1) then
        cutoffC (2 * ((N : ℝ) * (gradLift N X.val (i + 1) - gradLift N X.val i)) / ((N : ℝ) * ℓ) ^ ε) *
          cutoffC (2 / (((N : ℝ) * ℓ) ^ ε * ((N : ℝ) * (gradLift N X.val (i + 1) - gradLift N X.val i))))
      else 1) := fun i _ => by
    split_ifs
    · exact mul_nonneg (cutoffC_mem_Icc _).1 (cutoffC_mem_Icc _).1
    · exact zero_le_one
  obtain ⟨hpA, hpB⟩ := pos_pos_of_mul_pos (Finset.prod_nonneg hA0) h
  constructor
  · intro i hi k hw hk0 hk2
    have hkI : k ∈ Finset.Icc (-((N : ℤ) / 2)) ((N : ℤ) / 2) := by
      rw [Finset.mem_Icc]
      have h1 := neg_abs_le k
      have h2 := le_abs_self k
      omega
    have hin := pos_factor_of_prod_pos hA0 hpA hi
    have hfac := pos_factor_of_prod_pos
      (fun k _ => (ite_cutoff_mem_Icc _ _).1) hin hkI
    simp only [ne_eq, hk0, hw, not_false_eq_true, and_self, ↓reduceIte] at hfac
    have hlt := (cutoffC_pos_iff _).mp hfac
    have hQ : 0 < ((N : ℝ) * ℓ) ^ ε * |(k : ℝ)| ^ (s / 2) :=
      mul_pos (hKε ε) (Real.rpow_pos_of_pos
        (abs_pos.mpr (Int.cast_ne_zero.mpr hk0)) _)
    rw [div_lt_iff₀ hQ] at hlt
    linarith
  · intro i hi hw
    have hin := pos_factor_of_prod_pos hB0 hpB hi
    simp only [hw, ↓reduceIte] at hin
    obtain ⟨h1, h2⟩ := pos_pos_of_mul_pos (cutoffC_mem_Icc _).1 hin
    rw [cutoffC_pos_iff, div_lt_iff₀ (hKε ε)] at h1
    have hg : (0 : ℝ) < (N : ℝ) * (gradLift N X.val (i + 1) - gradLift N X.val i) :=
      gap_pos X i
    have hKg : 0 < ((N : ℝ) * ℓ) ^ ε * ((N : ℝ) * (gradLift N X.val (i + 1) - gradLift N X.val i)) :=
      mul_pos (hKε ε) hg
    rw [cutoffC_pos_iff, div_lt_iff₀ hKg] at h2
    have h2' : 1 ≤ ((N : ℝ) * ℓ) ^ ε * ((N : ℝ) * (gradLift N X.val (i + 1) - gradLift N X.val i)) :=
      by linarith
    constructor
    · rw [Real.rpow_neg hK.le]
      calc (((N : ℝ) * ℓ) ^ ε)⁻¹
          ≤ (((N : ℝ) * ℓ) ^ ε)⁻¹ *
              (((N : ℝ) * ℓ) ^ ε * ((N : ℝ) * (gradLift N X.val (i + 1) - gradLift N X.val i))) :=
            le_mul_of_one_le_right (inv_nonneg.mpr (hKε ε).le) h2'
        _ = (N : ℝ) * (gradLift N X.val (i + 1) - gradLift N X.val i) :=
            inv_mul_cancel_left₀ (hKε ε).ne' _
    · linarith

end

end Riesz1
end
