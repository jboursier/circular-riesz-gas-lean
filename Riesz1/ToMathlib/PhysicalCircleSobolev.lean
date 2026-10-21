/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.WeightedFourierGrid
public import Riesz1.ToMathlib.Mollifier.RegularizationSobolev

/-!
# Physical normalization of circle Sobolev bounds

The integer-frequency seminorm is converted to physical frequency before the
circle length is allowed to vary. All convolutions and seminorms are the existing ones.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace Riesz1.Internal

theorem physical_sobolev_bound {L σ D : ℝ} (hL : 0 < L)
    (f : {f : UnitAddCircle → ℂ // MemLp f 2 volume})
    (hs : Summable (fun k : ℤ => if k = 0 then (0 : ℝ) else
      |2 * Real.pi * (k : ℝ) / L| ^ (2 * σ) * ‖fourierCoeff f.val k‖ ^ 2))
    (hb : L * (∑' k : ℤ, if k = 0 then (0 : ℝ) else
      |2 * Real.pi * (k : ℝ) / L| ^ (2 * σ) * ‖fourierCoeff f.val k‖ ^ 2) ≤ D) :
    ENNReal.ofReal (L * (2 * Real.pi / L) ^ (2 * σ)) * circleSobolevSq σ f ≤
      ENNReal.ofReal D := by
  let w := fun k : ℤ => if k = 0 then (0 : ℝ) else
    |2 * Real.pi * (k : ℝ) / L| ^ (2 * σ) * ‖fourierCoeff f.val k‖ ^ 2
  have hw (k : ℤ) : 0 ≤ w k := by dsimp [w]; split_ifs <;> positivity
  have hA : 0 ≤ L * (2 * Real.pi / L) ^ (2 * σ) := by positivity
  have he : ENNReal.ofReal (L * (2 * Real.pi / L) ^ (2 * σ)) * circleSobolevSq σ f =
      ENNReal.ofReal (L * ∑' k, w k) := by
    conv_rhs =>
      rw [ENNReal.ofReal_mul hL.le, ENNReal.ofReal_tsum_of_nonneg hw hs,
        ← ENNReal.tsum_mul_left]
    unfold circleSobolevSq
    rw [← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro k
    by_cases hk : k = 0
    · simp only [w, hk, ite_true, ENNReal.ofReal_zero, mul_zero]
    · simp only [w, hk, ite_false]
      rw [← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_mul hL.le]
      congr 1
      have he : |2 * Real.pi * (k : ℝ) / L| = (2 * Real.pi / L) * |(k : ℝ)| := by
        rw [abs_div, abs_mul, abs_of_pos hL, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
        ring
      rw [he, Real.mul_rpow (by positivity : 0 ≤ 2 * Real.pi / L) (abs_nonneg _)]
      ring
  rw [he]
  exact ENNReal.ofReal_le_ofReal hb

theorem physical_smoothing_bound {ρ : ℝ → ℝ} (hρ : IsCircleMollifier ρ)
    {L σ r D h : ℝ} (hL : 0 < L) (hh : 0 < h) (hhL : h / L ≤ 1)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (f : {f : UnitAddCircle → ℂ // MemLp f 2 volume})
    (hH : ENNReal.ofReal (L * (2 * Real.pi / L) ^ (2 * (σ + r))) *
      circleSobolevSq (σ + r) f ≤ ENNReal.ofReal D) :
    ENNReal.ofReal (L * (2 * Real.pi / L) ^ (2 * σ)) *
      circleSobolevSq σ (subL2 f (regularizeL2 hρ ⟨h / L, div_pos hh hL⟩ hhL f)) ≤
      ENNReal.ofReal (16 / (2 * Real.pi) ^ (2 * r) * D * h ^ (2 * r)) := by
  let A := L * (2 * Real.pi / L) ^ (2 * σ)
  let B := L * (2 * Real.pi / L) ^ (2 * (σ + r))
  let E := 16 / (2 * Real.pi) ^ (2 * r) * h ^ (2 * r)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have he : A * (16 * (h / L) ^ (2 * r)) = E * B := by
    dsimp [A, B, E]
    rw [show 2 * (σ + r) = 2 * σ + 2 * r by ring,
      Real.rpow_add (div_pos (by positivity) hL)]
    simp_rw [Real.div_rpow hh.le hL.le,
      Real.div_rpow (by positivity : 0 ≤ 2 * Real.pi) hL.le]
    field_simp
  have hb := mul_le_mul le_rfl (circleSobolevSq_subL2_le hρ
    ⟨h / L, div_pos hh hL⟩ hhL f hr hr1 (σ := σ))
    zero_le (show 0 ≤ ENNReal.ofReal A from zero_le)
  rw [← mul_assoc, ← ENNReal.ofReal_mul hA, he, ENNReal.ofReal_mul hE,
    mul_assoc] at hb
  have ht := mul_le_mul (show ENNReal.ofReal E ≤ ENNReal.ofReal E from le_rfl) hH zero_le zero_le
  rw [← ENNReal.ofReal_mul hE] at ht
  exact hb.trans (by simpa only [E, B, mul_assoc, mul_left_comm, mul_comm] using ht)

end Riesz1.Internal
