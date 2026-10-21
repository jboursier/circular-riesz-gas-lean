/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.APrioriComparisonSums

/-!
# Both summation assertions of a priori comparison

Part of Lemma 5.2 (the comparison part). The constants are chosen before
the number of particles, scale and subset of the window. The common
exponent `κ = 2` is independent of `ε`.
-/

@[expose] public section

noncomputable section

open Finset

namespace Riesz1

namespace APrioriComparison

theorem distance_pos {N : ℕ+} {i : Fin (N : ℕ)} (hi : i ≠ ⟨0, N.pos⟩) :
    1 ≤ labelDistToOne N i := by
  have hi0 : i.val ≠ 0 := by intro h; exact hi (Fin.ext h)
  rw [labelDistToOne_eq]
  have := i.isLt
  omega

/-- The head of the label sum, using at most two labels per distance. -/
theorem label_head_sum_le {N : ℕ+} {K s lam ε : ℝ} (hK : 1 ≤ K)
    (hs : 0 < s) (hs1 : s < 1) (hlam : 0 ≤ lam) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (J : Finset (Fin (N : ℕ))) (hJ : ∀ i ∈ J, i ≠ ⟨0, N.pos⟩) :
    ∑ i ∈ J, (if (labelDistToOne N i : ℝ) ≤ K ^ (1 + ε) then
      K ^ lam / (1 + (labelDistToOne N i : ℝ)) ^ (1 + lam) else 0) *
        (labelDistToOne N i : ℝ) ^ (s / 2) ≤
      2 * (1 + 2 / ε) * K ^ (2 * ε) * (K ^ lam + K ^ (s / 2)) := by
  have hf := sum_labelDist_le_two_mul
    (J.filter fun i => (labelDistToOne N i : ℝ) ≤ K ^ (1 + ε))
    (F := fun d => K ^ lam / (1 + (d : ℝ)) ^ (1 + lam) * (d : ℝ) ^ (s / 2))
    (by intro d; positivity)
    (T := Icc 1 ⌊K ^ (1 + ε)⌋₊) (by
      intro i hi
      obtain ⟨hiJ, hiK⟩ := mem_filter.mp hi
      exact mem_Icc.mpr ⟨distance_pos (hJ i hiJ), Nat.le_floor hiK⟩)
  have hb := head_sum_le hK hs hs1 hlam hε hε1 (Icc 1 ⌊K ^ (1 + ε)⌋₊) (by
    intro d hd
    obtain ⟨hd1, hdK⟩ := mem_Icc.mp hd
    exact ⟨hd1, (Nat.cast_le.mpr hdK).trans (Nat.floor_le (by positivity))⟩)
  have heq : (∑ i ∈ J, (if (labelDistToOne N i : ℝ) ≤ K ^ (1 + ε) then
      K ^ lam / (1 + (labelDistToOne N i : ℝ)) ^ (1 + lam) else 0) *
        (labelDistToOne N i : ℝ) ^ (s / 2)) =
      ∑ i ∈ J.filter (fun i => (labelDistToOne N i : ℝ) ≤ K ^ (1 + ε)),
        K ^ lam / (1 + (labelDistToOne N i : ℝ)) ^ (1 + lam) *
          (labelDistToOne N i : ℝ) ^ (s / 2) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  rw [heq]
  nlinarith

/-- The tail of the label sum. -/
theorem label_tail_sum_le {N : ℕ+} {K s ε : ℝ} (hK : 1 ≤ K)
    (hs : 0 < s) (hs1 : s < 1) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (J : Finset (Fin (N : ℕ))) :
    ∑ i ∈ J, (if K ^ (1 - ε) ≤ (labelDistToOne N i : ℝ) then
      K ^ (2 - s) / (1 + (labelDistToOne N i : ℝ)) ^ (3 - s) else 0) *
        (labelDistToOne N i : ℝ) ^ (s / 2) ≤
      2 * (1 + 1 / (2 - 3 * s / 2)) * K ^ (2 * ε) * K ^ (s / 2) := by
  let T := (Icc 1 (N : ℕ)).filter fun d : ℕ => K ^ (1 - ε) ≤ (d : ℝ)
  have hR : 1 ≤ K ^ (1 - ε) := Real.one_le_rpow hK (by linarith)
  have hf := sum_labelDist_le_two_mul
    (J.filter fun i => K ^ (1 - ε) ≤ (labelDistToOne N i : ℝ))
    (F := fun d => K ^ (2 - s) / (1 + (d : ℝ)) ^ (3 - s) * (d : ℝ) ^ (s / 2))
    (by intro d; positivity) (T := T) (by
      intro i hi
      obtain ⟨_, hiK⟩ := mem_filter.mp hi
      apply mem_filter.mpr
      refine ⟨mem_Icc.mpr ⟨?_, ?_⟩, hiK⟩
      · exact_mod_cast hR.trans hiK
      · rw [labelDistToOne_eq]; exact (min_le_left _ _).trans (Nat.le_of_lt i.isLt))
  have hb := tail_sum_le hK hs hs1 hε hε1 T (fun d hd => (mem_filter.mp hd).2)
  have heq : (∑ i ∈ J, (if K ^ (1 - ε) ≤ (labelDistToOne N i : ℝ) then
      K ^ (2 - s) / (1 + (labelDistToOne N i : ℝ)) ^ (3 - s) else 0) *
        (labelDistToOne N i : ℝ) ^ (s / 2)) =
      ∑ i ∈ J.filter (fun i => K ^ (1 - ε) ≤ (labelDistToOne N i : ℝ)),
        K ^ (2 - s) / (1 + (labelDistToOne N i : ℝ)) ^ (3 - s) *
          (labelDistToOne N i : ℝ) ^ (s / 2) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  rw [heq]
  nlinarith

/-- Harmonic bound for the extra, augmented weights. -/
theorem label_augmented_sum_le {N : ℕ+} {K s lam γ ε : ℝ} (hK : 1 ≤ K)
    (hs : 0 < s) (hγ : 0 ≤ γ) (hε : 0 < ε)
    (J : Finset (Fin (N : ℕ)))
    (hJ : J ⊆ (window N K γ).erase ⟨0, N.pos⟩) :
    ∑ i ∈ J, K ^ lam / (1 + (labelDistToOne N i : ℝ)) ^ (1 + s / 2) *
        (labelDistToOne N i : ℝ) ^ (s / 2) ≤
      2 * (1 + Real.log 4 + γ / ε) * K ^ ε * K ^ lam := by
  have hK0 : 0 < K := by linarith
  have hT : 1 ≤ 4 * K ^ γ := by have := Real.one_le_rpow hK hγ; linarith
  have hM : 1 ≤ ⌊4 * K ^ γ⌋₊ := Nat.le_floor (by simpa using hT)
  have hM0 : (0 : ℝ) < (⌊4 * K ^ γ⌋₊ : ℕ) := by exact_mod_cast (by omega : 0 < ⌊4 * K ^ γ⌋₊)
  have hlog : Real.log (⌊4 * K ^ γ⌋₊ : ℕ) ≤ Real.log 4 + γ * Real.log K := by
    calc Real.log (⌊4 * K ^ γ⌋₊ : ℕ) ≤ Real.log (4 * K ^ γ) :=
        Real.log_le_log hM0 (Nat.floor_le (by positivity))
      _ = _ := by rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hK0]
  have hlogK := mul_le_mul_of_nonneg_left (Real.log_le_rpow_div hK0.le hε) hγ
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hKe : 1 ≤ K ^ ε := Real.one_le_rpow hK hε.le
  have hh : ∑ d ∈ Icc 1 ⌊4 * K ^ γ⌋₊, (1 : ℝ) / d ≤
      (1 + Real.log 4 + γ / ε) * K ^ ε := by
    have h := sum_Icc_inv_le ⌊4 * K ^ γ⌋₊
    have heq : γ * (K ^ ε / ε) = (γ / ε) * K ^ ε := by ring
    rw [heq] at hlogK
    nlinarith
  have hf := sum_labelDist_le_two_mul J (F := fun d => (1 : ℝ) / d)
    (by intro d; positivity) (T := Icc 1 ⌊4 * K ^ γ⌋₊) (by
      intro i hi
      have hi' := mem_erase.mp (hJ hi)
      exact mem_Icc.mpr ⟨distance_pos hi'.1, Nat.le_floor (labelDist_le_of_mem_window hK hi'.2)⟩)
  have hterm : ∀ i ∈ J,
      K ^ lam / (1 + (labelDistToOne N i : ℝ)) ^ (1 + s / 2) *
          (labelDistToOne N i : ℝ) ^ (s / 2) ≤ K ^ lam * (1 / (labelDistToOne N i : ℝ)) := by
    intro i hi
    have hd : 0 < (labelDistToOne N i : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (distance_pos (mem_erase.mp (hJ hi)).1))
    have hden : (labelDistToOne N i : ℝ) ^ (1 + s / 2) ≤
        (1 + (labelDistToOne N i : ℝ)) ^ (1 + s / 2) :=
      Real.rpow_le_rpow hd.le (by linarith) (by linarith)
    calc _ ≤ K ^ lam / (labelDistToOne N i : ℝ) ^ (1 + s / 2) *
          (labelDistToOne N i : ℝ) ^ (s / 2) :=
        mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_left (by positivity) (by positivity) hden) (by positivity)
      _ = _ := by rw [Real.rpow_add hd, Real.rpow_one]; field_simp
  calc _ ≤ ∑ i ∈ J, K ^ lam * (1 / (labelDistToOne N i : ℝ)) := Finset.sum_le_sum hterm
    _ = K ^ lam * ∑ i ∈ J, (1 / (labelDistToOne N i : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ K ^ lam * (2 * ((1 + Real.log 4 + γ / ε) * K ^ ε)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
    _ = _ := by ring

end APrioriComparison

/-- Both weight sums, with the explicit uniform exponent `κ = 2`. -/
theorem comparison_sums_le (s lam γ : ℝ) (hs : 0 < s) (hs1 : s < 1)
    (hlam : 0 ≤ lam) (hγ : 1 < γ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ+) (K : ℝ), 1 ≤ K →
      ∀ J : Finset (Fin (N : ℕ)), J ⊆ (window N K γ).erase ⟨0, N.pos⟩ →
        (∑ i ∈ J, comparisonWeight N K s lam ε i * (labelDistToOne N i : ℝ) ^ (s / 2) ≤
          C * K ^ (2 * ε) * (K ^ lam + K ^ (s / 2))) ∧
        (∑ i ∈ J, augmentedComparisonWeight N K s lam ε i *
            (labelDistToOne N i : ℝ) ^ (s / 2) ≤
          C * K ^ (2 * ε) * (K ^ lam + K ^ (s / 2))) := by
  let A := 2 * ((1 + 2 / ε) + (1 + 1 / (2 - 3 * s / 2)))
  let B := 2 * (1 + Real.log 4 + γ / ε)
  have hA : 0 < A := by
    have : 0 < 2 - 3 * s / 2 := by linarith
    dsimp [A]; positivity
  have hB : 0 < B := by
    have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    have : 0 < γ := by linarith
    dsimp [B]; positivity
  refine ⟨A + B, by positivity, fun N K hK J hJ => ?_⟩
  have hK0 : 0 < K := by linarith
  have hJ0 : ∀ i ∈ J, i ≠ ⟨0, N.pos⟩ := fun i hi => (mem_erase.mp (hJ hi)).1
  have hh := APrioriComparison.label_head_sum_le hK hs hs1 hlam hε hε1 J hJ0
  have ht := APrioriComparison.label_tail_sum_le hK hs hs1 hε.le hε1 J
  have hbase : ∑ i ∈ J, comparisonWeight N K s lam ε i * (labelDistToOne N i : ℝ) ^ (s / 2) ≤
      A * K ^ (2 * ε) * (K ^ lam + K ^ (s / 2)) := by
    simp only [comparisonWeight, add_mul, Finset.sum_add_distrib]
    have hc : 0 ≤ 2 * (1 + 1 / (2 - 3 * s / 2)) * K ^ (2 * ε) := by
      have : 0 < 2 - 3 * s / 2 := by linarith
      positivity
    have hp : 0 ≤ K ^ lam := by positivity
    dsimp [A]
    nlinarith
  have he := APrioriComparison.label_augmented_sum_le (lam := lam) hK hs
    (by linarith : 0 ≤ γ) hε J hJ
  have hpow : K ^ ε ≤ K ^ (2 * ε) := Real.rpow_le_rpow_of_exponent_le hK (by linarith)
  have he' : ∑ i ∈ J, K ^ lam / (1 + (labelDistToOne N i : ℝ)) ^ (1 + s / 2) *
        (labelDistToOne N i : ℝ) ^ (s / 2) ≤ B * K ^ (2 * ε) * (K ^ lam + K ^ (s / 2)) := by
    change _ ≤ _ at he
    have hm := mul_le_mul_of_nonneg_left hpow hB.le
    have h := mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg hK0.le lam)
    have hn : 0 ≤ B * K ^ (2 * ε) * K ^ (s / 2) := by positivity
    dsimp [B] at *
    nlinarith
  have hb0 : 0 ≤ B * K ^ (2 * ε) * (K ^ lam + K ^ (s / 2)) := by positivity
  constructor
  · nlinarith
  · simp only [augmentedComparisonWeight, add_mul, Finset.sum_add_distrib]
    linarith

/-- **Both summation bounds** (part of Lemma 5.2, the comparison part).
One constant works for the original and augmented weights, with an
exponent chosen independently of `ε`. -/
theorem a_priori_comparison_summation (s lam γ : ℝ) (hs : 0 < s) (hs1 : s < 1)
    (hlam : 0 ≤ lam) (hγ : 1 < γ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ C : ℝ, 0 < C ∧
      ∀ (N : ℕ+) (K : ℝ), 1 ≤ K →
      ∀ J : Finset (Fin (N : ℕ)), J ⊆ (window N K γ).erase ⟨0, N.pos⟩ →
        (∑ i ∈ J, comparisonWeight N K s lam ε i * (labelDistToOne N i : ℝ) ^ (s / 2) ≤
          C * K ^ (κ * ε) * (K ^ lam + K ^ (s / 2))) ∧
        (∑ i ∈ J, augmentedComparisonWeight N K s lam ε i *
            (labelDistToOne N i : ℝ) ^ (s / 2) ≤
          C * K ^ (κ * ε) * (K ^ lam + K ^ (s / 2))) :=
  ⟨2, by norm_num, fun ε hε hε1 => comparison_sums_le s lam γ hs hs1 hlam hγ ε hε hε1⟩

end Riesz1

end
