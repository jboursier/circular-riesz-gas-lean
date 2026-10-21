/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopLocalizationAmplitude

/-!
# The cutoff agrees with the original derivative on the central ball

The global-tail support step of the localization part of Lemma 5.8.
The circle representative is retained explicitly, including across the seam.
-/

public section

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace Riesz1

/-- The centered representative realizes the circular distance. -/
theorem loopLocalization_rep_abs {ℓ : ℝ} (hℓ : 0 < ℓ) (u : ℝ) :
    |loopCircleRep ℓ u| = circDist ℓ⁻¹ u := by
  let n : ℤ := -⌊ℓ * u + 1 / 2⌋
  have he : loopCircleRep ℓ u = u + n * ℓ⁻¹ := by
    dsimp [loopCircleRep, n]
    push_cast
    ring
  have hmem := loopCircleRep_mem_Ico hℓ u
  have hhalf : 1 / (2 * ℓ) = ℓ⁻¹ / 2 := by field_simp
  rw [hhalf] at hmem
  have hq := circDist_abs_of_le (inv_pos.mpr hℓ)
    (abs_le.mpr ⟨hmem.1, hmem.2.le⟩)
  rw [← hq, he]
  exact circDist_add_int_mul (inv_pos.mpr hℓ) u n

/-- In the central ball the cutoff is exactly the opposite-point-shifted
original microscopic transport. -/
theorem loopLocalTransport_eq_scale_sub {N : ℕ+} {ℓ γ : ℝ}
    (hℓ : 0 < ℓ) (hP : GradPartial N ℓ γ) {χ ψ : ℝ → ℝ}
    (hχ1 : ∀ x : ℝ, |x| ≤ 1 / 8 → χ x = 1)
    (hp : Function.Periodic ψ ℓ⁻¹) {z : ℝ}
    (hz : circDist (N : ℝ) z ≤ gradM N ℓ γ / 8) :
    loopLocalTransport χ N ℓ γ ψ z =
      loopScaleField ((N : ℝ) * ℓ) ψ z - ((N : ℝ) * ℓ) * ψ (1 / (2 * ℓ)) := by
  let K := (N : ℝ) * ℓ
  let M := gradM N ℓ γ
  let q := loopCircleRep ℓ (z / K)
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hK : 0 < K := mul_pos hN hℓ
  have hM : 0 < M := Real.rpow_pos_of_pos hK γ
  have hscale : (N : ℝ) / K = ℓ⁻¹ := by dsimp [K]; field_simp
  have hq : |q| = circDist (N : ℝ) z / K := by
    rw [loopLocalization_rep_abs hℓ, ← hscale, circDist_scale hK]
  have harg : ℓ * q / gradT N ℓ γ = K * q / M := by
    simp only [gradT, hP, ↓reduceIte]
    dsimp [K, M]
    field_simp
  have hχ : χ (ℓ * q / gradT N ℓ γ) = 1 := by
    apply hχ1
    rw [harg, abs_div, abs_mul, abs_of_pos hK, abs_of_pos hM, hq,
      mul_div_cancel₀ _ hK.ne', div_le_iff₀ hM]
    linarith
  have hψq : ψ q = ψ (z / K) := by
    let n : ℤ := -⌊ℓ * (z / K) + 1 / 2⌋
    have he : q = z / K + n * ℓ⁻¹ := by
      dsimp [q, loopCircleRep, n]
      push_cast
      ring
    rw [he]
    exact hp.int_mul n _
  change K * (if GradPartial N ℓ γ then
    χ (ℓ * q / gradT N ℓ γ) * (ψ q - ψ (1 / (2 * ℓ))) else ψ (z / K)) = _
  rw [ite_eq_left hP, hχ, one_mul, hψq]
  change K * (ψ (z / K) - ψ (1 / (2 * ℓ))) =
    K * ψ (z / K) - K * ψ (1 / (2 * ℓ))
  ring

/-- The derivative of the difference vanishes on the central open ball. -/
theorem loopLocalization_difference_deriv_zero {N : ℕ+} {ℓ γ : ℝ}
    (hℓ : 0 < ℓ) (hP : GradPartial N ℓ γ) {χ ψ : ℝ → ℝ}
    (hχ1 : ∀ x : ℝ, |x| ≤ 1 / 8 → χ x = 1)
    (hp : Function.Periodic ψ ℓ⁻¹) {z : ℝ}
    (hz : circDist (N : ℝ) z < gradM N ℓ γ / 8) :
    deriv (loopScaleField ((N : ℝ) * ℓ) ψ - loopLocalTransport χ N ℓ γ ψ) z = 0 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have hc : Continuous (circDist (N : ℝ)) := by
    apply LipschitzWith.continuous (K := 1)
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
      ((abs_circDist_sub_circDist_le (a := x) (b := y) hN).trans
        (circDist_le_abs_self hN _))
  have he : (loopScaleField ((N : ℝ) * ℓ) ψ - loopLocalTransport χ N ℓ γ ψ) =ᶠ[𝓝 z]
      fun _ => ((N : ℝ) * ℓ) * ψ (1 / (2 * ℓ)) := by
    filter_upwards [(isOpen_lt hc continuous_const).mem_nhds hz] with u hu
    change loopScaleField ((N : ℝ) * ℓ) ψ u - loopLocalTransport χ N ℓ γ ψ u = _
    rw [loopLocalTransport_eq_scale_sub hℓ hP hχ1 hp hu.le]
    ring
  rw [he.deriv_eq, deriv_const]

end Riesz1

end
