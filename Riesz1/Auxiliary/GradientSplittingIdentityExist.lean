/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.GradientSplittingIdentity

/-!
# Existence of the principal values and of the background integrals

For every real `x`, both principal values of the `V`-integrands exist in the `y`-frame, and
the background integrand `y ↦ Z(x, y) h(y - x)` is interval integrable on the
window `B`. These are the integrals that the fields `V`, `W` and the loop `H_γ` require.
-/

@[expose] public section

open Set MeasureTheory Filter Topology intervalIntegral
open scoped ContDiff

namespace Riesz1

noncomputable section

/-- Both principal values of the `V`-integrands exist at every real `x`: the two truncated integrals
over the window `B` converge as `δ ↓ 0`. -/
lemma gradPV_exists {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ γ : ℝ} (hℓ0 : 0 < ℓ)
    (hp : Function.Periodic ψ (1 / ℓ)) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {N : ℕ+}
    (hsupp : GradPartial N ℓ γ → ∀ y : ℝ, (∀ m : ℤ, gradT N ℓ γ / 4 ≤ |y - m|) → ψ (y / ℓ) = 0)
    (x : ℝ) :
    ∃ LA LB : ℝ,
      Tendsto (fun δ : ℝ => ∫ y in gradBLo N ℓ γ x..gradBHi N ℓ γ x,
        Set.indicator {y : ℝ | ∀ m : ℤ, δ ≤ |y - x - m|}
          (fun y => gradZx ψ ℓ x y * gradKernelH s (y - x)) y) (𝓝[>] 0) (𝓝 LA) ∧
      Tendsto (fun δ : ℝ => ∫ y in gradBLo N ℓ γ x..gradBHi N ℓ γ x,
        Set.indicator {y : ℝ | ∀ m : ℤ, δ ≤ |y - x - m|}
          (fun y => gradZ ψ ℓ x y * deriv (gradKernelH s) (y - x)) y) (𝓝[>] 0) (𝓝 LB) := by
  by_cases hpart : GradPartial N ℓ γ
  · obtain ⟨ht, ht2⟩ := gradT_partial_bounds hℓ0 hpart
    obtain ⟨LA, LB, hA, hB, -⟩ :=
      gradV_identity_partial hψ hℓ0 hp hs0 hs1 ht ht2 (hsupp hpart) x
    have hlo : gradBLo N ℓ γ x - x = -gradT N ℓ γ - x := by
      unfold gradBLo
      rw [ite_eq_left hpart]
    have hhi : gradBHi N ℓ γ x - x = gradT N ℓ γ - x := by
      unfold gradBHi
      rw [ite_eq_left hpart]
    have hA' : Tendsto (fun δ : ℝ => ∫ v in (gradBLo N ℓ γ x - x)..(gradBHi N ℓ γ x - x),
        (gradAllowed δ).indicator (fun v => (fun y => gradZx ψ ℓ x y * gradKernelH s (y - x)) (x + v))
          v) (𝓝[>] 0) (𝓝 LA) := by
      rw [hlo, hhi]
      simpa only [add_sub_cancel_left] using hA
    have hB' : Tendsto (fun δ : ℝ => ∫ v in (gradBLo N ℓ γ x - x)..(gradBHi N ℓ γ x - x),
        (gradAllowed δ).indicator
          (fun v => (fun y => gradZ ψ ℓ x y * deriv (gradKernelH s) (y - x)) (x + v)) v)
        (𝓝[>] 0) (𝓝 LB) := by
      rw [hlo, hhi]
      simpa only [add_sub_cancel_left] using hB
    exact ⟨LA, LB, tendsto_gradPV_integral_of_tendsto N ℓ γ x (f := fun y => gradZx ψ ℓ x y
      * gradKernelH s (y - x)) hA', tendsto_gradPV_integral_of_tendsto N ℓ γ x
      (f := fun y => gradZ ψ ℓ x y * deriv (gradKernelH s) (y - x)) hB'⟩
  · have hlo : gradBLo N ℓ γ x - x = -1 / 2 := by
      unfold gradBLo
      rw [ite_eq_right hpart]
      ring
    have hhi : gradBHi N ℓ γ x - x = 1 / 2 := by
      unfold gradBHi
      rw [ite_eq_right hpart]
      ring
    obtain ⟨LA, LB, hA, hB, -⟩ := gradV_identity_full hψ hℓ0 hp hs0 hs1 x
    have hA' : Tendsto (fun δ : ℝ => ∫ v in (gradBLo N ℓ γ x - x)..(gradBHi N ℓ γ x - x),
        (gradAllowed δ).indicator (fun v => (fun y => gradZx ψ ℓ x y * gradKernelH s (y - x)) (x + v))
          v) (𝓝[>] 0) (𝓝 LA) := by
      rw [hlo, hhi]
      simpa only [add_sub_cancel_left] using hA
    have hB' : Tendsto (fun δ : ℝ => ∫ v in (gradBLo N ℓ γ x - x)..(gradBHi N ℓ γ x - x),
        (gradAllowed δ).indicator
          (fun v => (fun y => gradZ ψ ℓ x y * deriv (gradKernelH s) (y - x)) (x + v)) v)
        (𝓝[>] 0) (𝓝 LB) := by
      rw [hlo, hhi]
      simpa only [add_sub_cancel_left] using hB
    exact ⟨LA, LB, tendsto_gradPV_integral_of_tendsto N ℓ γ x (f := fun y => gradZx ψ ℓ x y
      * gradKernelH s (y - x)) hA', tendsto_gradPV_integral_of_tendsto N ℓ γ x
      (f := fun y => gradZ ψ ℓ x y * deriv (gradKernelH s) (y - x)) hB'⟩

/-- The background integrand `y ↦ Z(x, y) h(y - x)` is interval integrable on the window `B`, for
every real `x`. -/
lemma intervalIntegrable_gradBackground {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) {ℓ γ : ℝ}
    (hℓ0 : 0 < ℓ) (hp : Function.Periodic ψ (1 / ℓ)) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (N : ℕ+) (x : ℝ) :
    IntervalIntegrable (fun y => gradZ ψ ℓ x y * gradKernelH s (y - x)) volume
      (gradBLo N ℓ γ x) (gradBHi N ℓ γ x) := by
  have hfun : (fun y => gradZ ψ ℓ x y * gradKernelH s (y - x))
      = fun y => gradD ψ ℓ x (y - x) * deriv (hurwitzKernel s) (y - x) := by
    funext y
    have h := gradZ_mul_kernelH_shift hψ hℓ0.ne' s x (y - x)
    rwa [add_sub_cancel] at h
  have h1 := intervalIntegrable_gradD_mul_deriv (hψ.of_le (by simp)) hℓ0 hp hs0 hs1 x
    (gradBLo N ℓ γ x - x) (gradBHi N ℓ γ x - x)
  have h2 := h1.comp_sub_right x
  rw [hfun]
  simpa only [sub_add_cancel] using h2

end

end Riesz1
