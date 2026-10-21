/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopSizeBiasComplete
public import Riesz1.Auxiliary.LoopLocalMomentsDefs

/-!
# The first-gap cutoff in the anchoring argument

The anchoring part of Lemma 5.8: the anchored cutoff vanishes
when its size weight exceeds `K^ε`. The first two labels belong to the
cutoff window even in the two-particle and `K = 1` cases.
-/

public section

noncomputable section

open Finset

namespace Riesz1

/-- Both endpoints of the first gap are in every admissible window. -/
theorem loopAnchoring_first_labels {N : ℕ+} (hN : 2 ≤ (N : ℕ))
    {ℓ γ : ℝ} (hK : 1 ≤ (N : ℝ) * ℓ) (hγ : 0 ≤ γ) :
    (0 : ℤ) ∈ gradLabels N ℓ γ ∧ gradInWindow N ℓ γ 1 := by
  have hM : (1 : ℝ) ≤ gradM N ℓ γ := Real.one_le_rpow hK hγ
  have hfloor : (1 : ℤ) ≤ ⌊gradM N ℓ γ⌋ := by
    exact Int.le_floor.mpr (by simpa using hM)
  constructor
  · unfold gradLabels
    split_ifs <;> simp only [Finset.mem_Icc, Finset.mem_Ico] <;> omega
  · intro hP
    simp only [gradLabels, hP, ↓reduceIte, Finset.mem_Icc]
    omega

/-- The cutoff is zero at or above the first-gap threshold. This is a
pointwise statement on the entire anchored-coordinate carrier. -/
theorem loopAnchoring_cutoff_zero {n : ℕ} {s γ ε ℓ : ℝ}
    (_hℓ : 0 < ℓ) (hK : 1 ≤ ((n + 1).succPNat : ℝ) * ℓ) (hγ : 0 ≤ γ)
    (y : Fin (n + 1) → ℝ)
    (hw : (((n + 1).succPNat : ℝ) * ℓ) ^ ε ≤ loopSizeWeight n y) :
    loopCutoff s γ ε (n + 1).succPNat ℓ (anchorVector y) = 0 := by
  have hK0 : 0 < ((n + 1).succPNat : ℝ) * ℓ := by linarith
  have hpow := Real.rpow_pos_of_pos hK0 ε
  obtain ⟨h0, h1⟩ := loopAnchoring_first_labels (N := (n + 1).succPNat)
    (by simp) hK (by linarith : 0 ≤ 2 * γ)
  have hgap : ((n + 1).succPNat : ℝ) *
      (gradLift (n + 1).succPNat (anchorVector y) (0 + 1) -
        gradLift (n + 1).succPNat (anchorVector y) 0) = loopSizeWeight n y := by
    have hN : (1 : ℤ) < ((n + 1).succPNat : ℤ) := by simp
    have hi : gradIndex (n + 1).succPNat 1 = (0 : Fin (n + 1)).succ := by
      apply Fin.ext
      change (1 % (((n + 1).succPNat : ℕ) : ℤ)).toNat = 1
      rw [Int.emod_eq_of_lt (by norm_num) hN]
      rfl
    have hz : gradLift (n + 1).succPNat (anchorVector y) 0 = 0 :=
      gradLift_zero_of_anchor (anchorVector_zero y)
    rw [zero_add, hz, sub_zero]
    unfold gradLift
    rw [hi, Int.ediv_eq_zero_of_lt (by norm_num) hN]
    simp only [Int.cast_zero, add_zero, anchorVector_succ, loopSizeWeight,
      Nat.succPNat_coe, Nat.cast_succ]
  have hc : cutoffC (2 * loopSizeWeight n y / (((n + 1).succPNat : ℝ) * ℓ) ^ ε) = 0 := by
    have hr : 2 ≤ 2 * loopSizeWeight n y / (((n + 1).succPNat : ℝ) * ℓ) ^ ε := by
      rw [le_div_iff₀ hpow]
      linarith
    simp only [cutoffC, max_eq_left (by linarith :
      2 - 2 * loopSizeWeight n y / (((n + 1).succPNat : ℝ) * ℓ) ^ ε ≤ 0), min_eq_right zero_le_one]
  unfold loopCutoff
  apply mul_eq_zero_of_right
  apply Finset.prod_eq_zero h0
  simp only [zero_add] at hgap ⊢
  simp only [h1, ↓reduceIte]
  rw [hgap, hc, zero_mul]

/-- The localized cutoff loop vanishes above the size threshold. -/
theorem loopAnchoring_F_zero {n : ℕ} {s γ ε ℓ : ℝ}
    (hℓ : 0 < ℓ) (hK : 1 ≤ ((n + 1).succPNat : ℝ) * ℓ) (hγ : 0 ≤ γ)
    (χ ψ : ℝ → ℝ) (y : Fin (n + 1) → ℝ)
    (hw : (((n + 1).succPNat : ℝ) * ℓ) ^ ε ≤ loopSizeWeight n y) :
    loopCutoffF χ s γ ε (n + 1).succPNat ℓ ψ (anchorVector y) = 0 := by
  rw [loopCutoffF, loopAnchoring_cutoff_zero hℓ hK hγ y hw, zero_mul]

end Riesz1

end
