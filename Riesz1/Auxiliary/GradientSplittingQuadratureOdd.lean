/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingQuadraturePartialCells
public import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Odd kernel tails in a partial window

The quadrature part of Lemma 5.7. Odd cancellation removes a symmetric
interval of increments. When the particle's label is in the middle half of the window,
the remaining increments have modulus at least `n/2`.
-/

@[expose] public section

open Finset

namespace Riesz1

/-- An odd function sums to zero on a symmetric integer interval, with zero omitted. -/
lemma gradPartial_sum_symmetric_eq_zero (m : ℤ) (f : ℤ → ℝ)
    (hf : ∀ k : ℤ, k ≠ 0 → f (-k) = -f k) :
    ∑ k ∈ (Finset.Icc (-m) m).erase 0, f k = 0 := by
  refine Finset.sum_involution (fun k _ => -k) ?_ ?_ ?_ ?_
  · intro k hk
    rw [hf k (Finset.mem_erase.mp hk).1]
    ring
  · intro k hk _ he
    have hk0 := (Finset.mem_erase.mp hk).1
    omega
  · intro k hk
    simp only [Finset.mem_erase, Finset.mem_Icc] at hk ⊢
    constructor
    · omega
    · constructor <;> omega
  · intro k hk
    ring

/-- The surviving part of an odd sum lies in the tails, with at most `2n+1` terms.
This is an internal finite-sum estimate, independent of the kernel. -/
lemma gradPartial_odd_tail_count_bound {n i : ℤ} (hi : 2 * |i| ≤ n)
    (f : ℤ → ℝ) (hf : ∀ k : ℤ, k ≠ 0 → f (-k) = -f k) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ k : ℤ, k ≠ 0 → (n : ℝ) / 2 ≤ |(k : ℝ)| → |k| ≤ 2 * n → |f k| ≤ B) :
    |∑ k ∈ (Finset.Icc (-n - i) (n - i)).erase 0, f k| ≤ (2 * (n : ℝ) + 1) * B := by
  classical
  let A := (Finset.Icc (-n - i) (n - i)).erase 0
  let C := (Finset.Icc (-(n - |i|)) (n - |i|)).erase 0
  have hiabs : -|i| ≤ i ∧ i ≤ |i| := ⟨neg_abs_le i, le_abs_self i⟩
  have hC : C ⊆ A := by
    intro k hk
    simp only [C, A, Finset.mem_erase, Finset.mem_Icc] at hk ⊢
    refine ⟨hk.1, ?_, ?_⟩ <;> omega
  have hc0 : ∑ k ∈ C, f k = 0 := gradPartial_sum_symmetric_eq_zero _ f hf
  have hsplit : ∑ k ∈ A, f k = ∑ k ∈ A \ C, f k := by
    have hh := Finset.sum_sdiff (f := f) hC
    rw [hc0, add_zero] at hh
    exact hh.symm
  have hcard : ((A \ C).card : ℝ) ≤ 2 * (n : ℝ) + 1 := by
    have hsub : A \ C ⊆ Finset.Icc (-n - i) (n - i) :=
      (Finset.sdiff_subset).trans (Finset.erase_subset _ _)
    have hle := Finset.card_le_card hsub
    have he := Int.card_Icc_of_le (a := -n - i) (b := n - i) (by omega)
    have hc : ((Finset.Icc (-n - i) (n - i)).card : ℝ) = 2 * (n : ℝ) + 1 := by
      have he' := congrArg (Int.cast (R := ℝ)) he
      push_cast at he'
      linarith
    exact (Nat.cast_le.mpr hle).trans hc.le
  change |∑ k ∈ A, f k| ≤ _
  rw [hsplit]
  calc |∑ k ∈ A \ C, f k| ≤ ∑ k ∈ A \ C, |f k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ A \ C, B := by
      apply Finset.sum_le_sum
      intro k hk
      obtain ⟨hkA, hkC⟩ := Finset.mem_sdiff.mp hk
      have hkA' := hkA
      simp only [A, Finset.mem_erase, Finset.mem_Icc] at hkA'
      have hkC' : ¬ (-(n - |i|) ≤ k ∧ k ≤ n - |i|) := by
        intro h
        exact hkC (Finset.mem_erase.mpr ⟨hkA'.1, Finset.mem_Icc.mpr h⟩)
      have hlarge : n ≤ 2 * |k| := by
        have hi' := abs_nonneg i
        rcases le_total 0 k with hk0 | hk0
        · rw [abs_of_nonneg hk0]
          omega
        · rw [abs_of_nonpos hk0]
          omega
      have hlargeR : (n : ℝ) / 2 ≤ |(k : ℝ)| := by
        have he : (n : ℝ) ≤ 2 * |(k : ℝ)| := by exact_mod_cast hlarge
        linarith
      apply hb k hkA'.1 hlargeR
      rw [abs_le]
      constructor <;> omega
    _ = ((A \ C).card : ℝ) * B := by simp
    _ ≤ (2 * (n : ℝ) + 1) * B := mul_le_mul_of_nonneg_right hcard hB

/-- Microscopic scaling of the first kernel derivative. -/
lemma gradPartial_kernel_deriv_scale {s N v : ℝ} (hN : 0 < N) :
    N ^ (-s) * |v / N| ^ (-s - 1) = N * |v| ^ (-s - 1) := by
  rw [abs_div, abs_of_pos hN, Real.div_rpow (abs_nonneg v) hN.le, div_eq_mul_inv,
    ← Real.rpow_neg hN.le]
  calc N ^ (-s) * (|v| ^ (-s - 1) * N ^ (-(-s - 1))) =
      (N ^ (-s) * N ^ (-(-s - 1))) * |v| ^ (-s - 1) := by ring
    _ = N * |v| ^ (-s - 1) := by
      rw [← Real.rpow_add hN, show -s + -(-s - 1) = 1 by ring, Real.rpow_one]

/-- The odd reference sum is `O(N n^{-s})` for middle-half labels. -/
theorem gradPartial_odd_sum_bound {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ γ : ℝ) (i : ℤ),
      GradPartial N ℓ γ → 1 ≤ ⌊gradM N ℓ γ⌋ → 2 * |i| ≤ ⌊gradM N ℓ γ⌋ →
      |(N : ℝ) ^ (-s) * ∑ j ∈ (gradLabels N ℓ γ).erase i,
          deriv (gradKernelH s) (((gradPathIncr N ℓ γ i j : ℤ) : ℝ) / N)|
        ≤ C * (N : ℝ) * (⌊gradM N ℓ γ⌋ : ℝ) ^ (-s) := by
  obtain ⟨Cg, hCg, hg⟩ := gradSplit_derivative_bounds s hs0 hs1
  refine ⟨3 * Cg * 2 ^ (s + 1), by positivity, ?_⟩
  intro N ℓ γ i hP hn hi
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hnR : (1 : ℝ) ≤ (⌊gradM N ℓ γ⌋ : ℝ) := by exact_mod_cast hn
  let f : ℤ → ℝ := fun k => (N : ℝ) ^ (-s) * deriv (gradKernelH s) ((k : ℝ) / N)
  have hf : ∀ k : ℤ, k ≠ 0 → f (-k) = -f k := by
    intro k _
    have heq : deriv (gradKernelH s) (-(k : ℝ) / N) =
        -deriv (gradKernelH s) ((k : ℝ) / N) := by
      have he : (fun x : ℝ => gradKernelH s (-x)) = gradKernelH s :=
        funext (gradSplit_gradKernelH_even s)
      have hd := congrArg (fun g : ℝ → ℝ => deriv g ((k : ℝ) / N)) he
      rw [deriv_comp_neg] at hd
      rw [neg_div]
      linarith
    simp only [f, Int.cast_neg, heq, mul_neg]
  have h8 := gradPartial_eight_mul_lt hP
  have hB : 0 ≤ Cg * (N : ℝ) * ((⌊gradM N ℓ γ⌋ : ℝ) / 2) ^ (-s - 1) := by positivity
  have hb : ∀ k : ℤ, k ≠ 0 → (⌊gradM N ℓ γ⌋ : ℝ) / 2 ≤ |(k : ℝ)| →
      |k| ≤ 2 * ⌊gradM N ℓ γ⌋ → |f k| ≤
        Cg * (N : ℝ) * ((⌊gradM N ℓ γ⌋ : ℝ) / 2) ^ (-s - 1) := by
    intro k hk hklo hkhi
    have hkr : |(k : ℝ)| ≤ 2 * (⌊gradM N ℓ γ⌋ : ℝ) := by exact_mod_cast hkhi
    have h8R : 8 * (⌊gradM N ℓ γ⌋ : ℝ) < (N : ℝ) := by exact_mod_cast h8
    have hr0 : 0 < |(k : ℝ) / (N : ℝ)| := abs_pos.mpr (div_ne_zero (Int.cast_ne_zero.mpr hk) hN.ne')
    have hr1 : |(k : ℝ) / (N : ℝ)| ≤ 3 / 4 := by
      rw [abs_div, abs_of_pos hN, div_le_iff₀ hN]
      linarith
    have hg1 := (hg _ hr0 hr1).2 1 (by norm_num)
    simp only [iteratedDeriv_one, Nat.cast_one] at hg1
    have hpow := Real.rpow_le_rpow_of_nonpos (by linarith : 0 < (⌊gradM N ℓ γ⌋ : ℝ) / 2)
      hklo (by linarith : -s - 1 ≤ 0)
    calc |f k| = (N : ℝ) ^ (-s) * |deriv (gradKernelH s) ((k : ℝ) / N)| := by
          simp only [f, abs_mul, abs_of_nonneg (Real.rpow_nonneg hN.le _)]
      _ ≤ (N : ℝ) ^ (-s) * (Cg * |(k : ℝ) / N| ^ (-s - 1)) := by gcongr
      _ = Cg * (N : ℝ) * |(k : ℝ)| ^ (-s - 1) := by
          rw [mul_left_comm, gradPartial_kernel_deriv_scale hN, mul_assoc]
      _ ≤ _ := by gcongr
  have hsum := gradPartial_odd_tail_count_bound hi f hf hB hb
  rw [← sum_labels_erase_partial hP i f] at hsum
  simp only [f, ← Finset.mul_sum] at hsum
  refine hsum.trans ?_
  have hc : 2 * (⌊gradM N ℓ γ⌋ : ℝ) + 1 ≤ 3 * (⌊gradM N ℓ γ⌋ : ℝ) := by linarith
  have he : ((⌊gradM N ℓ γ⌋ : ℝ) / 2) ^ (-s - 1) =
      2 ^ (s + 1) * (⌊gradM N ℓ γ⌋ : ℝ) ^ (-s - 1) := by
    rw [Real.div_rpow (by linarith) (by norm_num),
      show -s - 1 = -(s + 1) by ring, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul,
      mul_comm]
  calc _ ≤ (3 * (⌊gradM N ℓ γ⌋ : ℝ)) *
        (Cg * (N : ℝ) * ((⌊gradM N ℓ γ⌋ : ℝ) / 2) ^ (-s - 1)) :=
      mul_le_mul_of_nonneg_right hc hB
    _ = _ := by
      rw [he]
      have hp : (⌊gradM N ℓ γ⌋ : ℝ) * (⌊gradM N ℓ γ⌋ : ℝ) ^ (-s - 1) =
          (⌊gradM N ℓ γ⌋ : ℝ) ^ (-s) := by
        conv_lhs => lhs; rw [← Real.rpow_one (⌊gradM N ℓ γ⌋ : ℝ)]
        rw [← Real.rpow_add (by linarith : 0 < (⌊gradM N ℓ γ⌋ : ℝ))]
        congr 1
        ring
      calc _ = (3 * Cg * 2 ^ (s + 1) * (N : ℝ)) *
            ((⌊gradM N ℓ γ⌋ : ℝ) * (⌊gradM N ℓ γ⌋ : ℝ) ^ (-s - 1)) := by ring
        _ = _ := by rw [hp]

/-- The boundary part of the odd principal value has the same `O(N n^{-s})` size
as the reference tails. It is retained explicitly, rather than discarded. -/
theorem gradPartial_kernel_boundary_bound {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ γ x : ℝ),
      GradPartial N ℓ γ → 1 ≤ ⌊gradM N ℓ γ⌋ →
      |(N : ℝ) * x| ≤ gradM N ℓ γ / 2 →
      |(N : ℝ) ^ (1 - s) *
          (gradKernelH s (gradT N ℓ γ - x) - gradKernelH s (-gradT N ℓ γ - x))|
        ≤ (C * (N : ℝ)) * (⌊gradM N ℓ γ⌋ : ℝ) ^ (-s) := by
  obtain ⟨Cg, hCg, hg⟩ := gradSplit_derivative_bounds s hs0 hs1
  refine ⟨2 * Cg * 2 ^ s, by positivity, ?_⟩
  intro N ℓ γ x hP hn hx
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hnR : (1 : ℝ) ≤ (⌊gradM N ℓ γ⌋ : ℝ) := by exact_mod_cast hn
  have hf := Int.floor_le (gradM N ℓ γ)
  have hM : 0 < gradM N ℓ γ := by linarith
  have ht : gradT N ℓ γ = gradM N ℓ γ / N := by simp [gradT, hP]
  have hp : (N : ℝ) ^ (1 - s) = (N : ℝ) * (N : ℝ) ^ (-s) := by
    rw [Real.rpow_sub hN, Real.rpow_one, Real.rpow_neg hN.le]
    ring
  have hpoint : ∀ v : ℝ, gradM N ℓ γ / 2 ≤ |v| → |v| ≤ 2 * gradM N ℓ γ →
      (N : ℝ) ^ (1 - s) * |gradKernelH s (v / N)| ≤
        Cg * (N : ℝ) * 2 ^ s * (⌊gradM N ℓ γ⌋ : ℝ) ^ (-s) := by
    intro v hv0 hv1
    have hr0 : 0 < |v / (N : ℝ)| := by
      rw [abs_div, abs_of_pos hN]
      exact div_pos (by linarith) hN
    have hr1 : |v / (N : ℝ)| ≤ 3 / 4 := by
      rw [abs_div, abs_of_pos hN, div_le_iff₀ hN]
      linarith [hP]
    have hb := (hg _ hr0 hr1).2 0 (by norm_num)
    simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero] at hb
    have hpow : |v| ^ (-s) ≤ ((⌊gradM N ℓ γ⌋ : ℝ) / 2) ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
    have he : ((⌊gradM N ℓ γ⌋ : ℝ) / 2) ^ (-s) =
        2 ^ s * (⌊gradM N ℓ γ⌋ : ℝ) ^ (-s) := by
      rw [Real.div_rpow (by linarith) (by norm_num),
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul, mul_comm]
    calc (N : ℝ) ^ (1 - s) * |gradKernelH s (v / N)|
        ≤ (N : ℝ) ^ (1 - s) * (Cg * |v / N| ^ (-s)) := by gcongr
      _ = Cg * (N : ℝ) * |v| ^ (-s) := by
        rw [hp]
        calc _ = Cg * (N : ℝ) * ((N : ℝ) ^ (-s) * |v / N| ^ (-s)) := by ring
          _ = _ := by rw [gradCell_scale_rpow hN]
      _ ≤ Cg * (N : ℝ) * ((⌊gradM N ℓ γ⌋ : ℝ) / 2) ^ (-s) := by gcongr
      _ = _ := by rw [he]; ring
  have ha := abs_le.mp hx
  have hl : gradM N ℓ γ / 2 ≤ |-gradM N ℓ γ - (N : ℝ) * x| ∧
      |-gradM N ℓ γ - (N : ℝ) * x| ≤ 2 * gradM N ℓ γ := by
    rw [abs_of_neg (by linarith)]
    constructor <;> linarith
  have hr : gradM N ℓ γ / 2 ≤ |gradM N ℓ γ - (N : ℝ) * x| ∧
      |gradM N ℓ γ - (N : ℝ) * x| ≤ 2 * gradM N ℓ γ := by
    rw [abs_of_pos (by linarith)]
    constructor <;> linarith
  have h0 := hpoint _ hl.1 hl.2
  have h1 := hpoint _ hr.1 hr.2
  have he0 : (-gradM N ℓ γ - (N : ℝ) * x) / N = -gradT N ℓ γ - x := by
    rw [ht]; field_simp
  have he1 : (gradM N ℓ γ - (N : ℝ) * x) / N = gradT N ℓ γ - x := by
    rw [ht]; field_simp
  rw [he0] at h0
  rw [he1] at h1
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hN.le _)]
  have htri := mul_le_mul_of_nonneg_left
    (abs_sub (gradKernelH s (gradT N ℓ γ - x)) (gradKernelH s (-gradT N ℓ γ - x)))
    (Real.rpow_nonneg hN.le (1 - s))
  nlinarith

/-- The complete odd contribution in `gradV2_partial_split`, including its boundary term. -/
theorem gradPartial_odd_contribution_bound {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ γ x : ℝ) (i : ℤ),
      GradPartial N ℓ γ → 1 ≤ ⌊gradM N ℓ γ⌋ →
      2 * |i| ≤ ⌊gradM N ℓ γ⌋ → |(N : ℝ) * x| ≤ gradM N ℓ γ / 2 →
      |(N : ℝ) ^ (1 - s) *
          (gradKernelH s (gradT N ℓ γ - x) - gradKernelH s (-gradT N ℓ γ - x))
        - (N : ℝ) ^ (-s) * ∑ j ∈ (gradLabels N ℓ γ).erase i,
            deriv (gradKernelH s) (((gradPathIncr N ℓ γ i j : ℤ) : ℝ) / N)|
        ≤ C * (N : ℝ) * (⌊gradM N ℓ γ⌋ : ℝ) ^ (-s) := by
  obtain ⟨Co, hCo, ho⟩ := gradPartial_odd_sum_bound hs0 hs1
  obtain ⟨Cb, hCb, hb⟩ := gradPartial_kernel_boundary_bound hs0 hs1
  refine ⟨Cb + Co, by positivity, ?_⟩
  intro N ℓ γ x i hP hn hi hx
  have ho' := ho N ℓ γ i hP hn hi
  have hb' := hb N ℓ γ x hP hn hx
  refine (abs_sub _ _).trans ?_
  calc _ ≤ (Cb * (N : ℝ)) * (⌊gradM N ℓ γ⌋ : ℝ) ^ (-s)
        + Co * (N : ℝ) * (⌊gradM N ℓ γ⌋ : ℝ) ^ (-s) := add_le_add hb' ho'
    _ = _ := by ring

end Riesz1
