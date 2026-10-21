/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.MollifierPointwise.Basic
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Tactic

/-!
# Existence of a smooth, even probability mollifier

A normalized radial bump of outer radius `1/4` satisfies the support
requirement of `IsMollifier`. Its integral is strictly positive,
so normalization uses the actual mass of the bump.
-/

public section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1

/-- A mollifier exists independently of all model parameters. -/
theorem exists_isMollifier : ∃ ρ : ℝ → ℝ, IsMollifier ρ := by
  let b : ContDiffBump (0 : ℝ) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩
  refine ⟨b.normed volume, b.contDiff_normed, b.nonneg_normed,
    b.normed_neg, ?_, b.integral_normed⟩
  rw [b.tsupport_normed_eq]
  intro x hx
  have hx' : |x| ≤ 1 / 4 := by
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, b] using hx
  constructor <;> linarith [le_abs_self x, neg_le_abs x]

end Riesz1
