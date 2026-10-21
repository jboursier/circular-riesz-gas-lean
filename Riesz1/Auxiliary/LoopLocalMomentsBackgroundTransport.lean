/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopLocalMomentsBackground
public import Riesz1.Auxiliary.LoopLocalMomentsTransport

/-!
# The background moment bound

The entire deterministic `|C_bg|` assertion of the local moments part of
Lemma 5.8, including both window regimes.
The multiplicative constant is independent of the number of particles, the scale,
the profile and its envelope constant.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1

/-- The deterministic part of the localized-loop moment bound. The estimate is uniform
even in `γ > 1`, a generalization of the paper's fixed-`γ` assertion. -/
theorem loopLocalTransport_background_bound {s α : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (hα : s - 1 ≤ α) (hα2 : α < s / 2) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4))
    (hχ1 : ∀ x : ℝ, |x| ≤ 1 / 8 → χ x = 1) (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ γ : ℝ) (ψ : ℝ → ℝ) (C0 : ℝ),
      2 ≤ (N : ℕ) → 0 < ℓ → 1 ≤ (N : ℝ) * ℓ → 1 < γ → 0 ≤ C0 → ContDiff ℝ ∞ ψ →
      Function.Periodic ψ ℓ⁻¹ →
      (∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      (∀ t, |deriv (deriv ψ) t| ≤ C0 * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      IntervalIntegrable (fun z => ∫ u in loopLocalLo N ℓ γ..loopLocalHi N ℓ γ,
        loopArcKernel s N (loopLocalTransport χ N ℓ γ ψ) z u)
        volume (loopLocalLo N ℓ γ) (loopLocalHi N ℓ γ) ∧
      |loopLocalBackground s N ℓ γ (loopLocalTransport χ N ℓ γ ψ)| ≤
        C * C0 * ((N : ℝ) * ℓ) ^ ((1 - s + α) + 2 * γ) := by
  obtain ⟨A, hA, ha⟩ := loopLocalBackground_bound hs hs1
  obtain ⟨B, hB, hb⟩ := loopLocalTransport_deriv_bound hs hs1 hα hα2 hχ hχc hχs hχ1 hχ01
  refine ⟨A * (B + 1), by positivity, ?_⟩
  intro N ℓ γ ψ C0 hN hℓ hK hγ hC0 hψ hp hd hdd
  have hKpos : 0 < (N : ℝ) * ℓ := by linarith
  have hLip := (hb N ℓ γ ψ C0 hℓ hK hγ hC0 hψ hp hd hdd).2
  have hb0 := contDiff_loopLocalTransport hχ hψ hχs N hℓ γ
  have hp0 := loopLocalTransport_periodic (N := N) hℓ χ hp (γ := γ)
  obtain ⟨hi, hbg⟩ := ha N ℓ γ hN hℓ.le hK (by linarith) (hb0.of_le (by simp)) hp0 hLip
  refine ⟨hi, ?_⟩
  rw [Real.coe_toNNReal _ (by positivity)] at hbg
  have hpow : ((N : ℝ) * ℓ) ^ (1 - s + α) * gradM N ℓ γ ^ 2 =
      ((N : ℝ) * ℓ) ^ ((1 - s + α) + 2 * γ) := by
    unfold gradM
    rw [← Real.rpow_natCast, ← Real.rpow_mul hKpos.le, ← Real.rpow_add hKpos]
    congr 1
    ring
  calc |loopLocalBackground s N ℓ γ (loopLocalTransport χ N ℓ γ ψ)|
      ≤ A * (B * C0 * ((N : ℝ) * ℓ) ^ (1 - s + α)) * gradM N ℓ γ ^ 2 := hbg
    _ = A * B * C0 * ((N : ℝ) * ℓ) ^ ((1 - s + α) + 2 * γ) := by
      calc _ = A * B * C0 * (((N : ℝ) * ℓ) ^ (1 - s + α) * gradM N ℓ γ ^ 2) := by ring
        _ = _ := by rw [hpow]
    _ ≤ A * (B + 1) * C0 * ((N : ℝ) * ℓ) ^ ((1 - s + α) + 2 * γ) := by
      gcongr
      linarith

end Riesz1

end
