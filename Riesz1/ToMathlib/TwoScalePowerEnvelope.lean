/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-!
# A single power envelope for a two-scale kernel

A near singular power and a far first-order smoothing error share a weaker
power envelope. This retains the small factor `h^(1-s)` at every displacement.
-/

public section

namespace Riesz1.TwoScalePowerEnvelope

/-- Trade the near displacement power for the smoothing scale. -/
theorem near {s h d k : ℝ} (hs : s < 1) (_hh : 0 < h) (hd : 0 < d)
    (hdh : d ≤ h) : d ^ (-s - k) ≤ h ^ (1 - s) * d ^ (-1 - k) := by
  have hp := Real.rpow_le_rpow hd.le hdh (by linarith : 0 ≤ 1 - s)
  have he : d ^ (-s - k) = d ^ (1 - s) * d ^ (-1 - k) := by
    rw [← Real.rpow_add hd]
    congr 1
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hd.le _)

/-- Trade the far decay power for the smoothing scale. -/
theorem far {s h d k : ℝ} (hs : 0 ≤ s) (hh : 0 < h) (hd : 0 < d)
    (hhd : h ≤ d) : h * d ^ (-s - 1 - k) ≤ h ^ (1 - s) * d ^ (-1 - k) := by
  have hp := Real.rpow_le_rpow hh.le hhd hs
  have hhpow : h = h ^ (1 - s) * h ^ s := by
    rw [← Real.rpow_add hh]
    simp
  have hdpow : d ^ s * d ^ (-s - 1 - k) = d ^ (-1 - k) := by
    rw [← Real.rpow_add hd]
    congr 1
    ring
  calc h * d ^ (-s - 1 - k) = h ^ (1 - s) * (h ^ s * d ^ (-s - 1 - k)) := by
        rw [← mul_assoc, ← hhpow]
    _ ≤ h ^ (1 - s) * (d ^ s * d ^ (-s - 1 - k)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp (by positivity)) (by positivity)
    _ = _ := by rw [hdpow]

/-- Both pieces imply one global envelope, with no gap at the transition. -/
theorem of_piecewise {s h d k A v : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hh : 0 < h) (hd : 0 < d) (hk : 0 ≤ k) (hA : 0 ≤ A)
    (hnear : d ≤ h → v ≤ A * (d ^ (-s - k) + h ^ (-s - k)))
    (hfar : h < d → v ≤ A * h * d ^ (-s - 1 - k)) :
    v ≤ 2 * A * h ^ (1 - s) * d ^ (-1 - k) := by
  by_cases hdh : d ≤ h
  · have hm := Real.rpow_le_rpow_of_nonpos hd hdh (by linarith : -s - k ≤ 0)
    have hn := near hs1 hh hd hdh (k := k)
    calc v ≤ A * (d ^ (-s - k) + h ^ (-s - k)) := hnear hdh
      _ ≤ A * (2 * (h ^ (1 - s) * d ^ (-1 - k))) :=
        mul_le_mul_of_nonneg_left (by linarith) hA
      _ = _ := by ring
  · have hf := far hs0 hh hd (le_of_lt (lt_of_not_ge hdh)) (k := k)
    calc v ≤ A * h * d ^ (-s - 1 - k) := hfar (lt_of_not_ge hdh)
      _ ≤ A * (h ^ (1 - s) * d ^ (-1 - k)) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hf hA
      _ ≤ _ := by nlinarith [mul_nonneg hA (mul_nonneg
          (Real.rpow_nonneg hh.le (1 - s)) (Real.rpow_nonneg hd.le (-1 - k)))]

end Riesz1.TwoScalePowerEnvelope
