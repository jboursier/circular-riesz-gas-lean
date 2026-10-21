/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopCutoffFBound

/-!
# An explicit exponent for the anchored cutoff bound

The cutoff part of Lemma 5.8 requires the polynomial exponent to depend only
on `s`, `α`, `γ`, and `ε`. This version retains the explicit exponent from the
proof, so the statement certifies its independence of the smooth cutoff profile.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1

/-- The polynomial bound with exponent `(1-s+α) + 2γ + ε(s+1)` explicitly recorded. -/
theorem loopCutoffF_explicit_bound {s α γ ε : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hα : s - 1 ≤ α)
    (hα2 : α < s / 2) (hγ : 1 < γ) (hε0 : 0 < ε) (hεs : ε ≤ 1 - s / 2) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ Set.Ioo (-(1 / 4)) (1 / 4))
    (hχ1 : ∀ x : ℝ, |x| ≤ 1 / 8 → χ x = 1) (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (C0 : ℝ) (N : ℕ+) (ℓ : ℝ) (ψ : ℝ → ℝ) (y : Fin (N : ℕ) → ℝ),
      0 ≤ C0 → 2 ≤ (N : ℕ) → 0 < ℓ → 1 ≤ (N : ℝ) * ℓ → ContDiff ℝ ∞ ψ →
      Function.Periodic ψ ℓ⁻¹ →
      (∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      (∀ t, |deriv (deriv ψ) t| ≤ C0 * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      y ∈ orderedDomain N → y ⟨0, N.pos⟩ = 0 →
      |loopCutoffF χ s γ ε N ℓ ψ y| ≤ C * C0 * ((N : ℝ) * ℓ) ^ ((1 - s + α) + 2 * γ + ε * (s + 1)) := by
  obtain ⟨Cenv, hCenv0, henv⟩ := loopTransport_envelope hs0 hs1 hα hα2 hχ hχc hχs hχ1 hχ01
  obtain ⟨Cb, hCb, hb1, hb2⟩ := gradKernelH_bound hs0 hs1
  have hC : 0 ≤ Cb * (64 * 2 ^ (s + 1) + 256 / (1 - s)) * Cenv := by
    have h1 : (0 : ℝ) ≤ 256 / (1 - s) := div_nonneg (by norm_num) (by linarith)
    have h2 : (0 : ℝ) ≤ 64 * 2 ^ (s + 1) + 256 / (1 - s) :=
      add_nonneg (by positivity) h1
    exact mul_nonneg (mul_nonneg hCb.le h2) hCenv0
  refine ⟨Cb * (64 * 2 ^ (s + 1) + 256 / (1 - s)) * Cenv,
    hC, ?_⟩
  intro C0 N ℓ ψ y hC0 _hN2 hℓ hK hψ hper hd1 hd2 hy hy0
  have hK0 : 0 < (N : ℝ) * ℓ := by linarith
  have ha0 : 0 ≤ 1 - s + α := by linarith
  have hZ0 : 0 ≤ Cenv * C0 := mul_nonneg hCenv0 hC0
  have hZb0 : 0 ≤ Cenv * C0 * ((N : ℝ) * ℓ) ^ (1 - s + α) :=
    mul_nonneg hZ0 (Real.rpow_nonneg hK0.le _)
  -- the uniform divided-difference bound on the transport
  have hZ' : ∀ t, |deriv (loopTransport χ N ℓ γ ψ) t| ≤
      Cenv * C0 * ((N : ℝ) * ℓ) ^ (1 - s + α) := by
    intro t
    have h := (henv N ℓ γ ψ C0 hℓ hK hγ hC0 hψ hper hd1 hd2 t).1
    exact le_trans h (mul_le_mul_of_nonneg_left (gradWeightOne_le_rpow hs1 hK ha0) hZ0)
  have hZ : ∀ x y' : ℝ, |gradZ (loopTransport χ N ℓ γ ψ) ℓ x y'| ≤
      Cenv * C0 * ((N : ℝ) * ℓ) ^ (1 - s + α) :=
    fun x y' => gradZ_abs_le_const hZ'
  unfold loopCutoffF
  obtain ⟨hη0, hη1⟩ := loopCutoff_mem_Icc s γ ε ℓ y
  rcases eq_or_lt_of_le hη0 with h0 | hpos
  · rw [← h0, zero_mul, abs_zero]
    exact mul_nonneg (mul_nonneg hC hC0) (Real.rpow_nonneg hK0.le _)
  · have hev := gradEvent_of_loopCutoff_pos hℓ (⟨y, hy⟩ : Configuration N) hpos
    have hL := loopGradLoop_bound (ψ := loopTransport χ N ℓ γ ψ)
      (Zb := Cenv * C0 * ((N : ℝ) * ℓ) ^ (1 - s + α)) hs0 hs1 hCb.le hZb0 hb1 hb2 hZ
      hγ.le hε0 hεs hℓ hK hev hy0
    have hη : |loopCutoff s γ ε N ℓ y| ≤ 1 := by
      rw [abs_of_nonneg hη0]
      exact hη1
    have hmul : |loopCutoff s γ ε N ℓ y * gradLoop s (loopTransport χ N ℓ γ ψ) N ℓ γ y| ≤
        |gradLoop s (loopTransport χ N ℓ γ ψ) N ℓ γ y| := by
      rw [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) hη
    have e1 : gradM N ℓ γ ^ 2 = ((N : ℝ) * ℓ) ^ (2 * γ) := by
      unfold gradM
      rw [← Real.rpow_natCast, ← Real.rpow_mul hK0.le]
      congr 1
      push_cast
      ring
    have e2 : (((N : ℝ) * ℓ) ^ ε) ^ (s + 1) = ((N : ℝ) * ℓ) ^ (ε * (s + 1)) :=
      (Real.rpow_mul hK0.le ε (s + 1)).symm
    have e3 : ((N : ℝ) * ℓ) ^ (1 - s + α) * ((N : ℝ) * ℓ) ^ (2 * γ) *
        ((N : ℝ) * ℓ) ^ (ε * (s + 1)) =
        ((N : ℝ) * ℓ) ^ ((1 - s + α) + 2 * γ + ε * (s + 1)) := by
      rw [← Real.rpow_add hK0, ← Real.rpow_add hK0]
    have heq : Cb * (64 * 2 ^ (s + 1) + 256 / (1 - s)) *
        (Cenv * C0 * ((N : ℝ) * ℓ) ^ (1 - s + α)) * gradM N ℓ γ ^ 2 *
        (((N : ℝ) * ℓ) ^ ε) ^ (s + 1) =
        Cb * (64 * 2 ^ (s + 1) + 256 / (1 - s)) * Cenv * C0 *
          ((N : ℝ) * ℓ) ^ ((1 - s + α) + 2 * γ + ε * (s + 1)) := by
      rw [e1, e2, ← e3]
      ring
    calc |loopCutoff s γ ε N ℓ y * gradLoop s (loopTransport χ N ℓ γ ψ) N ℓ γ y|
        ≤ |gradLoop s (loopTransport χ N ℓ γ ψ) N ℓ γ y| := hmul
      _ ≤ Cb * (64 * 2 ^ (s + 1) + 256 / (1 - s)) *
            (Cenv * C0 * ((N : ℝ) * ℓ) ^ (1 - s + α)) * gradM N ℓ γ ^ 2 *
            (((N : ℝ) * ℓ) ^ ε) ^ (s + 1) := hL
      _ = Cb * (64 * 2 ^ (s + 1) + 256 / (1 - s)) * Cenv * C0 *
            ((N : ℝ) * ℓ) ^ ((1 - s + α) + 2 * γ + ε * (s + 1)) := heq


end Riesz1

end
