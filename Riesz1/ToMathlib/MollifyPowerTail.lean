/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.MollifyLocalDerivative

/-! # Preservation of power tails under local convolution -/

public section

open MeasureTheory

namespace Riesz1

/-- A negative power tail changes by at most `2^(-e)` on a window of radius
at most one centered at a point whose distance function is at least two. -/
theorem power_tail_window_bound {δ f : ℝ → ℝ} {C e h x : ℝ}
    (hδ : ∀ y z, δ y ≤ δ z + |y - z|) (he : e ≤ 0) (hC : 0 ≤ C)
    (hh : h ≤ 1) (hx : 2 ≤ δ x)
    (hf : ∀ y, 1 ≤ δ y → |f y| ≤ C * δ y ^ e) :
    ∀ y : ℝ, |y - x| < h → |f y| ≤ C * 2 ^ (-e) * δ x ^ e := by
  intro y hy
  have hxy := hδ x y
  rw [abs_sub_comm x y] at hxy
  have hy1 : 1 ≤ δ y := by linarith
  have hyhalf : δ x / 2 ≤ δ y := by linarith
  have hp := Real.rpow_le_rpow_of_nonpos (by linarith : 0 < δ x / 2) hyhalf he
  have hid : (δ x / 2) ^ e = δ x ^ e * 2 ^ (-e) := by
    simpa only [neg_neg] using div_two_rpow_neg (by linarith : 0 ≤ δ x) (p := -e)
  rw [hid] at hp
  exact (hf y hy1).trans (by nlinarith [mul_le_mul_of_nonneg_left hp hC])

/-- Convolution preserves a power tail wherever its window remains in the tail region. -/
theorem mollifyLine_power_tail {ρ f δ : ℝ → ℝ} (hρ : IsMollifier ρ)
    {C e h x : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hC : 0 ≤ C) (he : e ≤ 0)
    (hm : AEStronglyMeasurable f volume)
    (hδ : ∀ y z, δ y ≤ δ z + |y - z|)
    (hf : ∀ y, 1 ≤ δ y → |f y| ≤ C * δ y ^ e) (hx : 2 ≤ δ x) :
    |mollifyLine ρ h f x| ≤ C * 2 ^ (-e) * δ x ^ e := by
  exact (mollifyLine_abs_le_of_local hρ hh (by positivity) hm
    (power_tail_window_bound hδ he hC hh1 hx hf)).2

/-- The derivative tail is preserved using only local differentiability,
so singularities outside the convolution window cause no problem. -/
theorem deriv_mollifyLine_power_tail {ρ f δ : ℝ → ℝ} (hρ : IsMollifier ρ)
    {C e h x : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hC : 0 ≤ C) (he : e ≤ 0)
    (hi : LocallyIntegrable f volume)
    (hδ : ∀ y z, δ y ≤ δ z + |y - z|)
    (hd : ∀ y, 1 ≤ δ y → DifferentiableAt ℝ f y)
    (hf : ∀ y, 1 ≤ δ y → |deriv f y| ≤ C * δ y ^ e) (hx : 2 ≤ δ x) :
    |deriv (mollifyLine ρ h f) x| ≤ C * 2 ^ (-e) * δ x ^ e := by
  apply abs_deriv_mollifyLine_le_of_local hρ hh (by positivity) hi
  · intro y hy
    apply hd
    have ht := hδ x y
    rw [abs_sub_comm x y] at ht
    linarith
  · exact power_tail_window_bound hδ he hC hh1 hx hf

end Riesz1
