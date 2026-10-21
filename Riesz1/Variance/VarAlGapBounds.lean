/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.VarAlTransferBounds
public import Riesz1.Auxiliary.GradientSplittingGapMain

/-!
# The cutoff gap covector of the loop

The deterministic gap estimate used in Proposition 5.9.
The cutoff uses the larger window, the field and its covector use the
original window, and the power-loss coefficient is chosen before epsilon.
-/

@[expose] public section

noncomputable section

open Set Finset
open scoped ContDiff

namespace Riesz1

/-- Increasing the window exponent enlarges the admissible integer labels,
including when the larger window becomes full. -/
theorem varAl_gradInWindow_mono {N : ℕ+} {ℓ γ δ : ℝ} (hK : 1 ≤ (N : ℝ) * ℓ)
    (hγδ : γ ≤ δ) {j : ℤ} (hj : gradInWindow N ℓ γ j) : gradInWindow N ℓ δ j := by
  intro hpδ
  have hpow : gradM N ℓ γ ≤ gradM N ℓ δ := Real.rpow_le_rpow_of_exponent_le hK hγδ
  have hpγ : GradPartial N ℓ γ := hpow.trans_lt hpδ
  have hh := (mem_gradLabels_partial hpγ j).mp (hj hpγ)
  exact (mem_gradLabels_partial hpδ j).mpr ⟨by linarith [Int.floor_mono hpow],
    hh.2.trans (Int.floor_mono hpow)⟩

/-- A larger-window good event implies the smaller-window event. -/
theorem varAl_gradEvent_mono {N : ℕ+} {s γ δ ε ℓ : ℝ} {X : Fin (N : ℕ) → ℝ}
    (hℓ : 0 < ℓ) (hK : 1 ≤ (N : ℝ) * ℓ) (hγδ : γ ≤ δ)
    (hX : gradEvent s δ ε N ℓ X) : gradEvent s γ ε N ℓ X := by
  have hlarge (i j : ℤ) (hi : i ∈ gradLabels N ℓ γ) (hj : gradInWindow N ℓ γ j) :
      ¬GradPartial N ℓ δ ∨ (i ∈ gradLabels N ℓ δ ∧ j ∈ gradLabels N ℓ δ) := by
    by_cases hpδ : GradPartial N ℓ δ
    · right
      have hpγ : GradPartial N ℓ γ :=
        (Real.rpow_le_rpow_of_exponent_le hK hγδ).trans_lt hpδ
      exact ⟨varAl_gradInWindow_mono hK hγδ (fun _ => hi) hpδ,
        varAl_gradInWindow_mono hK hγδ hj hpδ⟩
    · exact Or.inl hpδ
  constructor
  · intro i hi k hk _hk0 hkN
    exact gradEvent_pair_bound hX hℓ i k hkN (hlarge i (i + k) hi hk)
  · intro i hi hk
    exact gradEvent_edge_bounds hX i (hlarge i (i + 1) hi hk)

/-- The squared gap covector after multiplication by the larger-window
cutoff, with exactly the uniformity in epsilon required in Proposition 5.9.
This is the deterministic input to the inverse-energy estimate. -/
theorem varAl_gap_covector_bound {s α γ : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hα : s - 1 ≤ α) (hα2 : α < s / 2) (hγ : 1 < γ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (χ : ℝ → ℝ), ContDiff ℝ ∞ χ → HasCompactSupport χ →
      tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4) →
      (∀ x : ℝ, |x| ≤ 1 / 8 → χ x = 1) → (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
      ∀ ε : ℝ, 0 < ε → ε < min (1 / 8) ((1 - s / 2) / 8) →
        ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ C₀ : ℝ) (ψ : ℝ → ℝ),
          2 ≤ (N : ℕ) → 0 < ℓ → ℓ ≤ 1 → 1 ≤ (N : ℝ) * ℓ → 0 ≤ C₀ →
          ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
          (∀ t, |deriv ψ t| ≤ C₀ * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
          (∀ t, |deriv (deriv ψ) t| ≤
            C₀ * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
          ∀ X ∈ orderedDomain N,
            (loopCutoff s γ ε N ℓ X) ^ 2 *
              (∑ e ∈ Ico (0 : ℤ) N,
                (gradWgap s (loopTransport χ N ℓ γ ψ) N ℓ γ X e) ^ 2) ≤
              C * C₀ ^ 2 * ((N : ℝ) * ℓ) ^ (κ * ε) *
                ((N : ℝ) * ℓ + ((N : ℝ) * ℓ) ^ (2 * (1 - s + α))) := by
  obtain ⟨κ, hκ, hb⟩ := gradient_splitting_gap hs0 hs1 hα hα2 hγ
  refine ⟨κ, hκ, fun χ hχ hχc hχs hχ1 hχ01 ε hε hεs => ?_⟩
  obtain ⟨Ce, hCe, he⟩ := loopTransport_envelope hs0 hs1 hα hα2 hχ hχc hχs hχ1 hχ01
  obtain ⟨C, hC, hc⟩ := hb ε hε hεs
  refine ⟨C * Ce ^ 2 + 1, by positivity, ?_⟩
  intro N ℓ C₀ ψ hN hℓ hℓ1 hK hC₀ hψ hp h1 h2 X hX
  have hbound : 0 ≤ (C * Ce ^ 2 + 1) * C₀ ^ 2 * ((N : ℝ) * ℓ) ^ (κ * ε) *
      ((N : ℝ) * ℓ + ((N : ℝ) * ℓ) ^ (2 * (1 - s + α))) := by positivity
  have hη := loopCutoff_mem_Icc s γ ε ℓ X
  rcases eq_or_lt_of_le hη.1 with hzero | hpos
  · rw [← hzero, sq, zero_mul, zero_mul]
    exact hbound
  · have hgood := varAl_gradEvent_mono hℓ hK (show γ ≤ 2 * γ by linarith)
      (gradEvent_of_loopCutoff_pos hℓ (⟨X, hX⟩ : Configuration N) hpos)
    have hψγ := contDiff_loopTransport hχ hψ hχs N hℓ γ
    have hpγ := loopTransport_periodic (N := N) (γ := γ) hℓ χ hp
    have h1γ := fun t => (he N ℓ γ ψ C₀ hℓ hK hγ hC₀ hψ hp h1 h2 t).1
    have hsq := (hc N ℓ (Ce * C₀) (loopTransport χ N ℓ γ ψ) X hN hℓ hℓ1 hK
      (mul_nonneg hCe hC₀) hψγ hpγ h1γ hX hgood).2.2.2
    have hηsq : (loopCutoff s γ ε N ℓ X) ^ 2 ≤ 1 := by nlinarith [hη.1, hη.2]
    calc (loopCutoff s γ ε N ℓ X) ^ 2 *
        (∑ e ∈ Ico (0 : ℤ) N, (gradWgap s (loopTransport χ N ℓ γ ψ) N ℓ γ X e) ^ 2)
        ≤ ∑ e ∈ Ico (0 : ℤ) N,
          (gradWgap s (loopTransport χ N ℓ γ ψ) N ℓ γ X e) ^ 2 :=
          mul_le_of_le_one_left (sum_nonneg fun _ _ => sq_nonneg _) hηsq
      _ ≤ C * (Ce * C₀) ^ 2 * ((N : ℝ) * ℓ) ^ (κ * ε) *
          ((N : ℝ) * ℓ + ((N : ℝ) * ℓ) ^ (2 * (1 - s + α))) := hsq
      _ ≤ (C * Ce ^ 2 + 1) * C₀ ^ 2 * ((N : ℝ) * ℓ) ^ (κ * ε) *
          ((N : ℝ) * ℓ + ((N : ℝ) * ℓ) ^ (2 * (1 - s + α))) := by
          have hpw : 0 ≤ ((N : ℝ) * ℓ) ^ (κ * ε) *
              ((N : ℝ) * ℓ + ((N : ℝ) * ℓ) ^ (2 * (1 - s + α))) := by positivity
          nlinarith [mul_nonneg (sq_nonneg C₀) hpw]

end Riesz1

end
