/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.MollifierPointwise.Line
public import Mathlib.Analysis.Convolution

/-! # The integral norm contracts under line mollification -/

public section

open MeasureTheory ContinuousLinearMap
open scoped Convolution

namespace Riesz1

/-- Nonnegative unit-mass convolution contracts the real integral norm. -/
theorem integral_abs_mollifyLine_le {ρ f : ℝ → ℝ} (hρ : IsMollifier ρ)
    {h : ℝ} (hh : 0 < h) (hf : Integrable f) :
    (∫ x : ℝ, |mollifyLine ρ h f x|) ≤ ∫ x : ℝ, |f x| := by
  let κ := scaledMollifier ρ h
  have hκ : Integrable κ := (contDiff_scaledMollifier hρ).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_scaledMollifier hρ hh)
  have heq : mollifyLine ρ h f = f ⋆ κ := rfl
  have hmajor (x : ℝ) : |(f ⋆ κ) x| ≤ ((fun y => |f y|) ⋆ κ) x := by
    change |∫ y : ℝ, f y * κ (x - y)| ≤ ∫ y : ℝ, |f y| * κ (x - y)
    calc
      _ ≤ ∫ y : ℝ, |f y * κ (x - y)| := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun y : ℝ => f y * κ (x - y))
      _ = _ := by
        apply integral_congr_ae
        exact ae_of_all _ fun y => by
          dsimp only
          rw [abs_mul, abs_of_nonneg (scaledMollifier_nonneg hρ hh _)]
  rw [heq]
  calc _ ≤ ∫ x : ℝ, ((fun y => |f y|) ⋆ κ) x :=
      integral_mono (hf.integrable_convolution (lsmul ℝ ℝ) hκ).abs
        (hf.abs.integrable_convolution (lsmul ℝ ℝ) hκ) hmajor
    _ = (∫ x : ℝ, |f x|) * ∫ x : ℝ, κ x := integral_convolution (lsmul ℝ ℝ) hf.abs hκ
    _ = _ := by rw [show (∫ x : ℝ, κ x) = 1 from integral_scaledMollifier hρ hh, mul_one]

end Riesz1
