/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Bridges.Mollifier
public import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Quantitative rapid decay of the mollifier multiplier

Each integer decay order has one bound chosen before the real frequency.
This supplies the multiplier estimate in Lemma 5.1.
-/

public section

open MeasureTheory
open scoped FourierTransform ContDiff

namespace Riesz1

/-- The real multiplier of a mollifier has decay of every integer order. -/
theorem mollifierFT_rapidDecay {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      (1 + |t| ^ m) * |mollifierFT ρ t| ≤ C := by
  let f : ℝ → ℂ := fun x => (ρ x : ℂ)
  have hfc : ContDiff ℝ ∞ f := Complex.ofRealCLM.contDiff.comp hρ.contDiff
  have hfs : HasCompactSupport f := by
    exact hρ.hasCompactSupport.comp_left (g := fun y : ℝ => (y : ℂ)) rfl
  have hs (k : ℕ) : HasCompactSupport (iteratedDeriv k f) := by
    induction k with
    | zero => simpa only [iteratedDeriv_zero] using hfs
    | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv
  have hi (k : ℕ) : Integrable (iteratedDeriv k f) :=
    (hfc.continuous_iteratedDeriv k (by simp)).integrable_of_hasCompactSupport (hs k)
  let C := (∫ x, ‖f x‖) + ((2 * Real.pi) ^ m)⁻¹ * ∫ x, ‖iteratedDeriv m f x‖
  have hC : 0 ≤ C := by
    dsimp [C]
    exact add_nonneg (integral_nonneg fun _ => norm_nonneg _)
      (mul_nonneg (by positivity) (integral_nonneg fun _ => norm_nonneg _))
  refine ⟨C + 1, by linarith, fun t => ?_⟩
  have hb := Real.one_add_pow_mul_norm_fourier_le (n := m)
    (hfc.of_le (by simp)) (fun k _ => hi k) t
  rw [show 𝓕 f t = (mollifierFT ρ t : ℂ) from mollifierFT_ofReal hρ.isCircleMollifier t,
    Complex.norm_real, Real.norm_eq_abs] at hb
  exact hb.trans (by dsimp [C]; linarith)

end Riesz1
