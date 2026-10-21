/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Tactic

/-!
# The reciprocal above a positive lower cutoff

The function `x ↦ (max a x)⁻¹` is globally Lipschitz for `a > 0`
and smooth away from its single corner at `a`.
-/

public section

open Set Filter Topology
open scoped ContDiff

namespace Riesz1

/-- Positive clamping gives a global Lipschitz reciprocal. -/
theorem lipschitzWith_inv_max {a : ℝ} (ha : 0 < a) :
    LipschitzWith ⟨(a * a)⁻¹, by positivity⟩ (fun x : ℝ => (max a x)⁻¹) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hx : 0 < max a x := ha.trans_le (le_max_left _ _)
  have hy : 0 < max a y := ha.trans_le (le_max_left _ _)
  have hd : a * a ≤ max a x * max a y :=
    mul_le_mul (le_max_left _ _) (le_max_left _ _) ha.le hx.le
  have hmax : |max a x - max a y| ≤ |x - y| := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul, id_eq] using
      ((LipschitzWith.id : LipschitzWith 1 (fun x : ℝ => x)).const_max a).dist_le_mul x y
  have he : (max a x)⁻¹ - (max a y)⁻¹ =
      (max a y - max a x) / (max a x * max a y) := by
    field_simp
  rw [Real.dist_eq, Real.dist_eq, he, abs_div, abs_of_pos (mul_pos hx hy), abs_sub_comm]
  change _ ≤ (a * a)⁻¹ * |x - y|
  calc
    _ ≤ |x - y| / (a * a) :=
      div_le_div₀ (abs_nonneg _) hmax (mul_pos ha ha) hd
    _ = _ := by ring

/-- Positive clamping introduces just one possible nonsmooth point. -/
theorem contDiffOn_inv_max {a : ℝ} (ha : 0 < a) :
    ContDiffOn ℝ ∞ (fun x : ℝ => (max a x)⁻¹) ({a} : Set ℝ)ᶜ := by
  intro x hx
  have hne : x ≠ a := by simpa only [mem_compl_iff, mem_singleton_iff] using hx
  apply ContDiffAt.contDiffWithinAt
  rcases lt_or_gt_of_ne hne with hx | hx
  · apply (contDiffAt_const (c := a⁻¹)).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hx] with y hy
    rw [max_eq_left hy.le]
  · apply (contDiffAt_inv ℝ (ha.trans hx).ne').congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hx] with y hy
    rw [max_eq_right hy.le]

end Riesz1
