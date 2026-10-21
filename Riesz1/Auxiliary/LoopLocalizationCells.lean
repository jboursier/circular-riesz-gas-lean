/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopLocalizationAmplitude
public import Riesz1.Auxiliary.LoopLocalMomentsTransport
public import Riesz1.Auxiliary.LoopCrude

/-!
# Polynomial bounds for the localized derivative cell sum

The global loop moment step of the localization part of Lemma 5.8.
Packing counts cells near the cutoff support, independently of the period.
-/

public section

noncomputable section

open Set Finset
open scoped ContDiff

namespace Riesz1

/-- At most two integer points of one period occupy each unit distance shell. -/
theorem loopLocalization_near_cell_count (N : ℕ+) {R : ℝ} (hR : 0 ≤ R) :
    (((range (N : ℕ)).filter (fun m : ℕ => circDist (N : ℝ) (m : ℝ) ≤ R)).card : ℝ) ≤
      2 * (R + 1) := by
  classical
  let S := (range (N : ℕ)).filter (fun m : ℕ => circDist (N : ℝ) (m : ℝ) ≤ R)
  let shell := fun m : ℕ => ⌊circDist (N : ℝ) (m : ℝ)⌋₊
  have hmaps : ∀ m ∈ S, shell m ∈ range (⌊R⌋₊ + 1) := by
    intro m hm
    rw [Finset.mem_range]
    have h := Nat.floor_le_floor (mem_filter.mp hm).2
    exact Nat.lt_succ_of_le h
  have hcount (k : ℕ) : ((S.filter (fun m => shell m = k)).card : ℝ) ≤ 2 := by
    have hsub : S.filter (fun m => shell m = k) ⊆
        (range (N : ℕ)).filter (fun m => ⌊circDist (N : ℝ) (0 + m)⌋₊ = k) := by
      intro m hm
      obtain ⟨hmS, hmk⟩ := mem_filter.mp hm
      exact mem_filter.mpr ⟨(mem_filter.mp hmS).1, by simpa [shell] using hmk⟩
    exact_mod_cast (Finset.card_le_card hsub).trans (card_shell_le_two (N : ℕ) N.pos 0 k)
  have hfib := sum_fiberwise_of_maps_to hmaps (fun _ : ℕ => (1 : ℝ))
  have hsum : (S.card : ℝ) ≤ 2 * (⌊R⌋₊ + 1 : ℕ) := by
    calc
      _ = ∑ k ∈ range (⌊R⌋₊ + 1), ((S.filter (fun m => shell m = k)).card : ℝ) := by
        simpa only [sum_const, nsmul_eq_mul, mul_one] using hfib.symm
      _ ≤ ∑ _k ∈ range (⌊R⌋₊ + 1), (2 : ℝ) := sum_le_sum fun k _ => hcount k
      _ = _ := by simp; ring
  change (S.card : ℝ) ≤ _
  have hfloor := Nat.floor_le hR
  push_cast at hsum
  linarith

/-- A derivative supported on a central circular ball contributes only a
bounded number of unit cells. The extra unit accounts for cells meeting its boundary. -/
theorem loopLocalization_cell_sum_of_support {N : ℕ+} {b : ℝ → ℝ} {R D : ℝ}
    (hR : 0 ≤ R) (hD : 0 ≤ D) (hd : ∀ z, |deriv b z| ≤ D)
    (hz : ∀ z, R < circDist (N : ℝ) z → deriv b z = 0) :
    ∑ m ∈ range (N : ℕ), cellSup b m ≤ 2 * (R + 2) * D := by
  classical
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hsup (m : ℕ) : cellSup b m ≤
      if circDist (N : ℝ) (m : ℝ) ≤ R + 1 then D else 0 := by
    unfold cellSup
    apply csSup_le
    · exact ⟨|deriv b m|, m, ⟨le_rfl, by linarith⟩, rfl⟩
    · rintro _ ⟨z, hzcell, rfl⟩
      split_ifs with hm
      · exact hd z
      · have hdist : circDist (N : ℝ) (m : ℝ) ≤ circDist (N : ℝ) z + 1 := by
          apply circDist_le_add_one_of_abs_sub_le hN
          rw [abs_sub_comm, abs_of_nonneg (by linarith [hzcell.1])]
          linarith [hzcell.2]
        change |deriv b z| ≤ 0
        rw [hz z (by linarith [not_le.mp hm]), abs_zero]
  calc
    _ ≤ ∑ m ∈ range (N : ℕ),
        if circDist (N : ℝ) (m : ℝ) ≤ R + 1 then D else 0 := sum_le_sum fun m _ => hsup m
    _ = (((range (N : ℕ)).filter
        (fun m : ℕ => circDist (N : ℝ) (m : ℝ) ≤ R + 1)).card : ℝ) * D := by
      rw [← sum_filter]; simp
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right
        (loopLocalization_near_cell_count N (R := R + 1) (by linarith)) hD
      convert h using 1
      ring

/-- The crude derivative cell sum of the actual localized transport is
polynomial in `K`, in both window regimes and throughout `K ≥ 1`. -/
theorem loopLocalTransport_cell_sum {s α : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (hα : s - 1 ≤ α) (hα2 : α < s / 2) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4))
    (hχ1 : ∀ x : ℝ, |x| ≤ 1 / 8 → χ x = 1) (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ γ : ℝ) (ψ : ℝ → ℝ) (C0 : ℝ),
      0 < ℓ → 1 ≤ (N : ℝ) * ℓ → 1 < γ → 0 ≤ C0 → ContDiff ℝ ∞ ψ →
      Function.Periodic ψ ℓ⁻¹ →
      (∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      (∀ t, |deriv (deriv ψ) t| ≤
        C0 * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      ∑ m ∈ range (N : ℕ), cellSup (loopLocalTransport χ N ℓ γ ψ) m ≤
        C * C0 * ((N : ℝ) * ℓ) ^ ((1 - s + α) + γ) := by
  obtain ⟨A, hA, hb⟩ := loopLocalTransport_deriv_bound hs hs1 hα hα2
    hχ hχc hχs hχ1 hχ01
  refine ⟨8 * (A + 1), by positivity, ?_⟩
  intro N ℓ γ ψ C0 hℓ hK hγ hC0 hψ hp hd hdd
  let K := (N : ℝ) * ℓ
  let M := gradM N ℓ γ
  let D := A * C0 * K ^ (1 - s + α)
  have hK0 : 0 < K := by dsimp [K]; linarith
  have hM : 1 ≤ M := Real.one_le_rpow hK (by linarith)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hb' : ∀ z, |deriv (loopLocalTransport χ N ℓ γ ψ) z| ≤ D :=
    (hb N ℓ γ ψ C0 hℓ hK hγ hC0 hψ hp hd hdd).1
  have hsum : ∑ m ∈ range (N : ℕ), cellSup (loopLocalTransport χ N ℓ γ ψ) m ≤
      8 * M * D := by
    by_cases hP : GradPartial N ℓ γ
    · have h := loopLocalization_cell_sum_of_support (N := N) (R := M / 4)
        (by linarith) hD hb'
        (fun z hz => loopLocalTransport_deriv_zero_of_circDist hℓ hP hχs ψ hz)
      exact h.trans (mul_le_mul_of_nonneg_right (by linarith : 2 * (M / 4 + 2) ≤ 8 * M) hD)
    · have hsup (m : ℕ) : cellSup (loopLocalTransport χ N ℓ γ ψ) m ≤ D := by
        apply csSup_le
        · exact ⟨|deriv (loopLocalTransport χ N ℓ γ ψ) m|, m, ⟨le_rfl, by linarith⟩, rfl⟩
        · rintro _ ⟨z, _, rfl⟩; exact hb' z
      calc
        _ ≤ ∑ _m ∈ range (N : ℕ), D := sum_le_sum fun m _ => hsup m
        _ = (N : ℝ) * D := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (by
          have h := not_lt.mp hP
          change (N : ℝ) ≤ 8 * gradM N ℓ γ
          linarith) hD
  have hpow : M * K ^ (1 - s + α) = K ^ ((1 - s + α) + γ) := by
    dsimp [M, gradM]
    rw [← Real.rpow_add hK0]
    congr 1
    ring
  calc
    _ ≤ 8 * M * D := hsum
    _ = 8 * A * C0 * K ^ ((1 - s + α) + γ) := by
      dsimp [D]
      calc
        _ = 8 * A * C0 * (M * K ^ (1 - s + α)) := by ring
        _ = _ := by rw [hpow]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right (by linarith) hC0

end Riesz1

end
