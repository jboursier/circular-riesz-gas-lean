/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopLocalMomentsDefs
public import Riesz1.Auxiliary.LoopCutoffPairBound

/-!
# The derivative bound for the microscopic localized transport

The first step in the proof of the local moments part of Lemma 5.8:
`‖b₀'‖∞ ≤ C C₀ K^(1-s+α)`, with `C` chosen before `N`, the scale and the profile.
This also gives a global Lipschitz bound, including across the antipodal seam.
-/

public section

noncomputable section

open Set
open scoped ContDiff

namespace Riesz1

/-- The uniform derivative and Lipschitz estimates used by the local moment proof.
Only the fixed cutoff and the exponent parameters enter `C`. -/
theorem loopLocalTransport_deriv_bound {s α : ℝ} (hs : 0 < s) (hs1 : s < 1)
    (hα : s - 1 ≤ α) (hα2 : α < s / 2) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ Ioo (-(1 / 4)) (1 / 4))
    (hχ1 : ∀ x : ℝ, |x| ≤ 1 / 8 → χ x = 1) (hχ01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ+) (ℓ γ : ℝ) (ψ : ℝ → ℝ) (C0 : ℝ),
      0 < ℓ → 1 ≤ (N : ℝ) * ℓ → 1 < γ → 0 ≤ C0 → ContDiff ℝ ∞ ψ →
      Function.Periodic ψ ℓ⁻¹ →
      (∀ t, |deriv ψ t| ≤ C0 * gradWeightOne s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      (∀ t, |deriv (deriv ψ) t| ≤ C0 * gradWeightTwo s (1 - s + α) ((N : ℝ) * ℓ) ℓ⁻¹ t) →
      (∀ z, |deriv (loopLocalTransport χ N ℓ γ ψ) z| ≤
        C * C0 * ((N : ℝ) * ℓ) ^ (1 - s + α)) ∧
      LipschitzWith (Real.toNNReal (C * C0 * ((N : ℝ) * ℓ) ^ (1 - s + α)))
        (loopLocalTransport χ N ℓ γ ψ) := by
  obtain ⟨C, hC, hb⟩ := loopTransport_envelope hs hs1 hα hα2 hχ hχc hχs hχ1 hχ01
  refine ⟨C, hC, fun N ℓ γ ψ C0 hℓ hK hγ hC0 hψ hp hd hdd => ?_⟩
  have hb0 : ∀ z, |deriv (loopLocalTransport χ N ℓ γ ψ) z| ≤
      C * C0 * ((N : ℝ) * ℓ) ^ (1 - s + α) := by
    intro z
    rw [deriv_loopLocalTransport hχ hψ hχs N hℓ γ z]
    apply (hb N ℓ γ ψ C0 hℓ hK hγ hC0 hψ hp hd hdd _).1.trans
    exact mul_le_mul_of_nonneg_left (gradWeightOne_le_rpow hs1 hK (by linarith))
      (mul_nonneg hC hC0)
  refine ⟨hb0, lipschitzWith_of_nnnorm_deriv_le
    ((contDiff_loopLocalTransport hχ hψ hχs N hℓ γ).differentiable (by simp)) ?_⟩
  intro z
  change |deriv (loopLocalTransport χ N ℓ γ ψ) z| ≤
    (Real.toNNReal (C * C0 * ((N : ℝ) * ℓ) ^ (1 - s + α)) : ℝ)
  rw [Real.coe_toNNReal _ (by positivity)]
  exact hb0 z

end Riesz1

end
