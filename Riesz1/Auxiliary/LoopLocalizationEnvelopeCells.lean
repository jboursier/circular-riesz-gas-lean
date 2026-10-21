/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopLocalizationCells
public import Riesz1.Auxiliary.LoopLocalizationLatticeTail

/-!
# Cell sums from the first derivative envelope

Uniform polynomial control of global tests, independent of the period. This
also controls the bounded scale range in Lemma 5.8.
-/

public section

noncomputable section

open Set Finset

namespace Riesz1.Internal

/-- Far from the origin a derivative envelope gives the integrable power
tail on each cell, including the cells at the periodic seam. -/
theorem loopLocalization_far_cell {s a K C0 : ℝ} (hs1 : s < 1)
    (hK : 1 ≤ K) (hC0 : 0 ≤ C0) (N : ℕ+) {b : ℝ → ℝ}
    (hd : ∀ z, |deriv b z| ≤ C0 * gradWeightOne s a K ((N : ℝ) / K) (z / K))
    (m : ℕ) (hm : K + 1 < circDist (N : ℝ) (m : ℝ)) :
    cellSup b m ≤ C0 * (2 : ℝ) ^ (2 - s) * K ^ (2 - s) *
      circDist (N : ℝ) (m : ℝ) ^ (s - 2) := by
  have hK0 : 0 < K := by linarith
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  apply csSup_le
  · exact ⟨|deriv b m|, m, ⟨le_rfl, by linarith⟩, rfl⟩
  · rintro _ ⟨z, hz, rfl⟩
    have hdist : circDist (N : ℝ) (m : ℝ) ≤ circDist (N : ℝ) z + 1 := by
      apply circDist_le_add_one_of_abs_sub_le hN
      rw [abs_sub_comm, abs_of_nonneg (by linarith [hz.1])]
      linarith [hz.2]
    have hzK : K ≤ circDist (N : ℝ) z := by linarith
    have hz0 : 0 < circDist (N : ℝ) z := hK0.trans_le hzK
    have hw : gradWeightOne s a K ((N : ℝ) / K) (z / K) =
        circDist (N : ℝ) z ^ (s - 2) * K ^ (2 - s) := by
      have h1 : 1 ≤ circDist ((N : ℝ) / K) (z / K) := by
        rw [circDist_scale hK0, le_div_iff₀ hK0, one_mul]
        exact hzK
      rw [gradWeightOne_of_one_le h1, circDist_scale hK0]
      have he : s - 2 = -(2 - s) := by ring
      rw [he, rpow_div_neg_eq hz0.le hK0]
    have hp := rpow_le_two_pow_mul_rpow hz0 (by linarith :
      0 < circDist (N : ℝ) (m : ℝ)) (by linarith :
      circDist (N : ℝ) (m : ℝ) ≤ 2 * circDist (N : ℝ) z) (by linarith : s - 2 ≤ 0)
    have he : -(s - 2) = 2 - s := by ring
    rw [he] at hp
    calc
      _ ≤ C0 * gradWeightOne s a K ((N : ℝ) / K) (z / K) := hd z
      _ = C0 * (circDist (N : ℝ) z ^ (s - 2) * K ^ (2 - s)) := by rw [hw]
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hp (by positivity : 0 ≤ K ^ (2 - s))) hC0
        convert h using 1
        ring

/-- The sum of derivative cell suprema under the first derivative envelope
is at most a fixed multiple of `C₀ K^(a+1)`. -/
theorem loopLocalization_cell_sum_envelope {s a K C0 : ℝ} (hs1 : s < 1)
    (ha : 0 ≤ a) (hK : 1 ≤ K) (hC0 : 0 ≤ C0) (N : ℕ+) {b : ℝ → ℝ}
    (hd : ∀ z, |deriv b z| ≤ C0 * gradWeightOne s a K ((N : ℝ) / K) (z / K)) :
    ∑ m ∈ range (N : ℕ), cellSup b m ≤
      (6 + (2 : ℝ) ^ (2 - s) * (2 * (1 + 1 / (1 - s)))) * C0 * K ^ (a + 1) := by
  classical
  let S := (range (N : ℕ)).filter (fun m : ℕ => circDist (N : ℝ) (m : ℝ) ≤ K + 1)
  let T := (range (N : ℕ)).filter (fun m : ℕ => ¬circDist (N : ℝ) (m : ℝ) ≤ K + 1)
  have hK0 : 0 < K := by linarith
  have hnear : ∑ m ∈ S, cellSup b m ≤ 6 * C0 * K ^ (a + 1) := by
    have hb (m : ℕ) : cellSup b m ≤ C0 * K ^ a := by
      apply csSup_le
      · exact ⟨|deriv b m|, m, ⟨le_rfl, by linarith⟩, rfl⟩
      · rintro _ ⟨z, _, rfl⟩
        exact (hd z).trans (mul_le_mul_of_nonneg_left
          (gradWeightOne_le_K_pow hs1 ha hK) hC0)
    calc
      _ ≤ ∑ _m ∈ S, C0 * K ^ a := sum_le_sum fun m _ => hb m
      _ = (S.card : ℝ) * (C0 * K ^ a) := by simp
      _ ≤ (2 * (K + 2)) * (C0 * K ^ a) := by
        have h := mul_le_mul_of_nonneg_right
          (loopLocalization_near_cell_count N (R := K + 1) (by linarith))
          (by positivity : 0 ≤ C0 * K ^ a)
        convert h using 1
        ring
      _ ≤ (6 * K) * (C0 * K ^ a) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by rw [Real.rpow_add hK0, Real.rpow_one]; ring
  have htail : ∑ m ∈ T, circDist (N : ℝ) (m : ℝ) ^ (s - 2) ≤
      (2 * (1 + 1 / (1 - s))) * K ^ (s - 1) := by
    have h := loopLocalization_lattice_tail N (a := 2 - s) (by linarith) hK T
      (filter_subset _ _) (by intro m hm; exact (by linarith [not_le.mp (mem_filter.mp hm).2]))
    have he1 : -(2 - s) = s - 2 := by ring
    have he2 : 2 - s - 1 = 1 - s := by ring
    have he3 : 1 - (2 - s) = s - 1 := by ring
    rwa [he1, he2, he3] at h
  have hfar : ∑ m ∈ T, cellSup b m ≤
      ((2 : ℝ) ^ (2 - s) * (2 * (1 + 1 / (1 - s)))) * C0 * K ^ (a + 1) := by
    have hpow : K ^ (2 - s) * K ^ (s - 1) = K := by
      rw [← Real.rpow_add hK0, show 2 - s + (s - 1) = 1 by ring, Real.rpow_one]
    have hKa : K ≤ K ^ (a + 1) := by
      calc K = K ^ (1 : ℝ) := (Real.rpow_one K).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hK (by linarith)
    calc
      _ ≤ ∑ m ∈ T, C0 * (2 : ℝ) ^ (2 - s) * K ^ (2 - s) *
          circDist (N : ℝ) (m : ℝ) ^ (s - 2) := by
        apply sum_le_sum
        intro m hm
        exact loopLocalization_far_cell hs1 hK hC0 N hd m (not_le.mp (mem_filter.mp hm).2)
      _ = (C0 * (2 : ℝ) ^ (2 - s) * K ^ (2 - s)) *
          ∑ m ∈ T, circDist (N : ℝ) (m : ℝ) ^ (s - 2) := (mul_sum ..).symm
      _ ≤ (C0 * (2 : ℝ) ^ (2 - s) * K ^ (2 - s)) *
          ((2 * (1 + 1 / (1 - s))) * K ^ (s - 1)) :=
        mul_le_mul_of_nonneg_left htail (by positivity)
      _ = ((2 : ℝ) ^ (2 - s) * (2 * (1 + 1 / (1 - s)))) * C0 * K := by
        calc
          _ = ((2 : ℝ) ^ (2 - s) * (2 * (1 + 1 / (1 - s)))) * C0 *
            (K ^ (2 - s) * K ^ (s - 1)) := by ring
          _ = _ := by rw [hpow]
      _ ≤ _ := mul_le_mul_of_nonneg_left hKa (by positivity)
  have hsplit := sum_filter_add_sum_filter_not (range (N : ℕ))
    (fun m : ℕ => circDist (N : ℝ) (m : ℝ) ≤ K + 1) (cellSup b)
  change (∑ m ∈ S, cellSup b m) + (∑ m ∈ T, cellSup b m) = _ at hsplit
  rw [← hsplit]
  calc
    _ ≤ 6 * C0 * K ^ (a + 1) +
        ((2 : ℝ) ^ (2 - s) * (2 * (1 + 1 / (1 - s)))) * C0 * K ^ (a + 1) :=
      add_le_add hnear hfar
    _ = _ := by ring

/-- If a derivative vanishes in a ball of radius `M/8`, its cell sum has
an integrable power tail once `M ≥ 64K`. -/
theorem loopLocalization_cell_sum_large_tail {s a K C0 M : ℝ} (hs1 : s < 1)
    (hK : 1 ≤ K) (hC0 : 0 ≤ C0) (hM : 64 * K ≤ M) (N : ℕ+) {b : ℝ → ℝ}
    (hd : ∀ z, |deriv b z| ≤ C0 * gradWeightOne s a K ((N : ℝ) / K) (z / K))
    (hz : ∀ z, circDist (N : ℝ) z < M / 8 → deriv b z = 0) :
    ∑ m ∈ range (N : ℕ), cellSup b m ≤
      ((2 : ℝ) ^ (2 - s) * (2 * (1 + 1 / (1 - s))) * (16 : ℝ) ^ (1 - s)) *
        C0 * K ^ (2 - s) * M ^ (s - 1) := by
  classical
  let T := (range (N : ℕ)).filter (fun m : ℕ => M / 16 ≤ circDist (N : ℝ) (m : ℝ))
  have hM0 : 0 < M := by linarith
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hzero (m : ℕ) (hm : ¬M / 16 ≤ circDist (N : ℝ) (m : ℝ)) : cellSup b m = 0 := by
    apply le_antisymm _ (cellSup_nonneg b m)
    apply csSup_le
    · exact ⟨|deriv b m|, m, ⟨le_rfl, by linarith⟩, rfl⟩
    · rintro _ ⟨z, hzc, rfl⟩
      change |deriv b z| ≤ 0
      have hdist : circDist (N : ℝ) z ≤ circDist (N : ℝ) (m : ℝ) + 1 := by
        apply circDist_le_add_one_of_abs_sub_le hN
        rw [abs_of_nonneg (by linarith [hzc.1])]
        linarith [hzc.2]
      rw [hz z (by linarith [not_le.mp hm]), abs_zero]
  have hsplit : ∑ m ∈ range (N : ℕ), cellSup b m = ∑ m ∈ T, cellSup b m := by
    rw [Finset.sum_filter]
    apply sum_congr rfl
    intro m _
    split_ifs with hm
    · rfl
    · exact hzero m hm
  have ht := loopLocalization_lattice_tail N (a := 2 - s) (by linarith)
    (R := M / 16) (by linarith) T (filter_subset _ _) (fun m hm => (mem_filter.mp hm).2)
  have he1 : -(2 - s) = s - 2 := by ring
  have he2 : 2 - s - 1 = 1 - s := by ring
  have he3 : 1 - (2 - s) = s - 1 := by ring
  rw [he1, he2, he3] at ht
  have hpow : (M / 16) ^ (s - 1) = M ^ (s - 1) * (16 : ℝ) ^ (1 - s) := by
    rw [show s - 1 = -(1 - s) by ring, rpow_div_neg_eq hM0.le (by norm_num)]
  rw [hsplit]
  calc
    _ ≤ ∑ m ∈ T, C0 * (2 : ℝ) ^ (2 - s) * K ^ (2 - s) *
        circDist (N : ℝ) (m : ℝ) ^ (s - 2) := by
      apply sum_le_sum
      intro m hm
      apply loopLocalization_far_cell hs1 hK hC0 N hd
      have h := (mem_filter.mp hm).2
      linarith
    _ = (C0 * (2 : ℝ) ^ (2 - s) * K ^ (2 - s)) *
        ∑ m ∈ T, circDist (N : ℝ) (m : ℝ) ^ (s - 2) := (mul_sum ..).symm
    _ ≤ (C0 * (2 : ℝ) ^ (2 - s) * K ^ (2 - s)) *
        ((2 * (1 + 1 / (1 - s))) * (M / 16) ^ (s - 1)) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ = _ := by rw [hpow]; ring

/-- The cell-tail estimate covers all scales, including `M/K < 64`. The
quadratic separation `K² ≤ M` is sufficient for that bounded range. -/
theorem loopLocalization_cell_sum_tail {s a : ℝ} (hs1 : s < 1) (ha : 0 ≤ a) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (K M C0 : ℝ) (b : ℝ → ℝ),
      1 ≤ K → K ^ (2 : ℝ) ≤ M → 0 ≤ C0 →
      (∀ z, |deriv b z| ≤ C0 * gradWeightOne s a K ((N : ℝ) / K) (z / K)) →
      (∀ z, circDist (N : ℝ) z < M / 8 → deriv b z = 0) →
      ∑ m ∈ range (N : ℕ), cellSup b m ≤ C * C0 * K ^ (2 - s) * M ^ (s - 1) := by
  let A := 6 + (2 : ℝ) ^ (2 - s) * (2 * (1 + 1 / (1 - s)))
  let B := (2 : ℝ) ^ (2 - s) * (2 * (1 + 1 / (1 - s))) * (16 : ℝ) ^ (1 - s)
  let D := A * (64 : ℝ) ^ (a + 1) * (4096 : ℝ) ^ (1 - s)
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨B + D, add_pos hB hD, ?_⟩
  intro N K M C0 b hK hKM hC0 hd hz
  have hK0 : 0 < K := by linarith
  have hM : 1 ≤ M := (Real.one_le_rpow hK (by norm_num : (0 : ℝ) ≤ 2)).trans hKM
  have hM0 : 0 < M := by linarith
  by_cases hlarge : 64 * K ≤ M
  · have h := loopLocalization_cell_sum_large_tail hs1 hK hC0 hlarge N hd hz
    apply h.trans
    gcongr
    linarith
  · have hsmall : M < 64 * K := not_le.mp hlarge
    have hK64 : K ≤ 64 := by
      rw [Real.rpow_two] at hKM
      nlinarith
    have hM4096 : M ≤ 4096 := by nlinarith
    have hKa : K ^ (a + 1) ≤ (64 : ℝ) ^ (a + 1) :=
      Real.rpow_le_rpow hK0.le hK64 (by linarith)
    have hKpow : 1 ≤ K ^ (2 - s) := Real.one_le_rpow hK (by linarith)
    have hMpow : (4096 : ℝ) ^ (s - 1) ≤ M ^ (s - 1) :=
      Real.rpow_le_rpow_of_nonpos hM0 hM4096 (by linarith)
    have hcancel : (4096 : ℝ) ^ (1 - s) * (4096 : ℝ) ^ (s - 1) = 1 := by
      rw [← Real.rpow_add (by norm_num), show 1 - s + (s - 1) = 0 by ring, Real.rpow_zero]
    have hfactor : 1 ≤ (4096 : ℝ) ^ (1 - s) * M ^ (s - 1) := by
      calc
        _ = (4096 : ℝ) ^ (1 - s) * (4096 : ℝ) ^ (s - 1) := hcancel.symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hMpow (by positivity)
    have hbase : A * C0 * K ^ (a + 1) ≤ D * C0 * K ^ (2 - s) * M ^ (s - 1) := by
      calc
        _ ≤ A * C0 * (64 : ℝ) ^ (a + 1) := mul_le_mul_of_nonneg_left hKa (by positivity)
        _ ≤ (A * C0 * (64 : ℝ) ^ (a + 1)) *
            ((4096 : ℝ) ^ (1 - s) * M ^ (s - 1)) :=
          le_mul_of_one_le_right (by positivity) hfactor
        _ ≤ (A * C0 * (64 : ℝ) ^ (a + 1)) *
            ((4096 : ℝ) ^ (1 - s) * M ^ (s - 1)) * K ^ (2 - s) :=
          le_mul_of_one_le_right (by positivity) hKpow
        _ = _ := by dsimp [D]; ring
    apply (loopLocalization_cell_sum_envelope hs1 ha hK hC0 N hd).trans
    apply hbase.trans
    gcongr
    linarith

end Riesz1.Internal

end
