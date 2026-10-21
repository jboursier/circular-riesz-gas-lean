/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-!
# Power bookkeeping for the loop variance

The final absorption step and the endpoint exponent in Proposition 5.9.
All estimates include `K = 1`. No asymptotic threshold is introduced.
-/

public section

namespace Riesz1.Internal

/-- The two main energy powers are bounded by their maximum. -/
theorem varAlLoop_power_sum {K b : ℝ} (hK : 1 ≤ K) :
    K + K ^ (2 * b) ≤ 2 * K ^ (max 1 (2 * b)) := by
  have h1 : K ≤ K ^ (max 1 (2 * b)) := by
    calc K = K ^ (1 : ℝ) := (Real.rpow_one K).symm
         _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hK (le_max_left _ _)
  have h2 := Real.rpow_le_rpow_of_exponent_le hK (le_max_right 1 (2 * b))
  linarith

/-- A positive small parameter can meet an analytic threshold and any
prescribed final loss, even if the total loss coefficient vanishes. -/
theorem varAlLoop_choose_epsilon {εstar κ ε : ℝ} (hstar : 0 < εstar)
    (hκ : 0 ≤ κ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < εstar ∧ κ * δ ≤ ε := by
  refine ⟨min (εstar / 2) (ε / (κ + 1)), lt_min (by positivity) (by positivity), ?_, ?_⟩
  · exact (min_le_left _ _).trans_lt (by linarith)
  · have hd := min_le_right (εstar / 2) (ε / (κ + 1))
    have hp : 0 < κ + 1 := by linarith
    have hδ : 0 ≤ min (εstar / 2) (ε / (κ + 1)) := by positivity
    have := (le_div_iff₀ hp).mp hd
    nlinarith

/-- Absorb the small losses after localization and measure transfer. -/
theorem varAlLoop_absorb {K b κ δ ε A B D : ℝ} (hK : 1 ≤ K)
    (hε : 0 ≤ ε) (hloss : κ * δ ≤ ε) (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D) :
    A * K ^ (κ * δ) * (K + K ^ (2 * b)) + B * Real.exp (-D * K ^ δ) ≤
      (2 * A + B) * K ^ (ε + max 1 (2 * b)) := by
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hpow := Real.rpow_le_rpow_of_exponent_le hK hloss
  have hsum := varAlLoop_power_sum (b := b) hK
  have hexp : Real.exp (-D * K ^ δ) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [Real.rpow_nonneg hK0.le δ])
  have hbase : 1 ≤ K ^ (ε + max 1 (2 * b)) :=
    Real.one_le_rpow hK (by linarith [le_max_left (1 : ℝ) (2 * b)])
  calc
    _ ≤ A * K ^ ε * (2 * K ^ (max 1 (2 * b))) + B * 1 := by
      gcongr
    _ ≤ (2 * A + B) * K ^ (ε + max 1 (2 * b)) := by
      have hb := mul_le_mul_of_nonneg_left hbase hB
      rw [Real.rpow_add hK0] at hb ⊢
      nlinarith

/-- At the endpoint one can move to a strictly interior exponent while
retaining the same maximum power, rather than spending any final loss. -/
theorem varAlLoop_endpoint_exponent {s : ℝ} (hs : s < 1) :
    ∃ α' : ℝ, s - 1 < α' ∧ α' < s / 2 ∧
      max 1 (2 * (1 - s + α')) = max 1 (2 * (1 - s + (s - 1))) := by
  refine ⟨s - 1 + min (1 / 4) ((1 - s / 2) / 2), ?_, ?_, ?_⟩
  · have : 0 < min (1 / 4 : ℝ) ((1 - s / 2) / 2) := lt_min (by norm_num) (by linarith)
    linarith
  · have := min_le_right (1 / 4 : ℝ) ((1 - s / 2) / 2)
    linarith
  · have := min_le_left (1 / 4 : ℝ) ((1 - s / 2) / 2)
    rw [max_eq_left (by linarith), max_eq_left (by linarith)]

/-- `N = 1` forces all three scale parameters to equal one. -/
theorem varAlLoop_one_scale {ℓ h : ℝ} (hℓ : ℓ ≤ 1) (hK : 1 ≤ (1 : ℝ) * ℓ)
    (hh : ((1 : ℝ) * ℓ)⁻¹ ≤ h) (hh1 : h ≤ 1) : ℓ = 1 ∧ h = 1 := by
  have he : ℓ = 1 := by linarith
  subst ℓ
  norm_num at hh
  exact ⟨rfl, le_antisymm hh1 hh⟩

end Riesz1.Internal
