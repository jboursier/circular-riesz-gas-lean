/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # The squared norm of a finite-dimensional vector in `L²`

Coordinate projections commute with the finite sum in the squared Euclidean norm.
-/

public section

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace Riesz1

theorem sum_norm_sq_l2_coordinates {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (u : Lp (EuclideanSpace ℝ ι) 2 μ) :
    (∑ i, ‖(EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 μ u‖ ^ 2) = ‖u‖ ^ 2 := by
  simp_rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  rw [← integral_finsetSum _ (fun i _ => L2.integrable_inner _ _)]
  apply integral_congr_ae
  have h (i : ι) := ContinuousLinearMap.coeFn_compLpL (EuclideanSpace.proj (𝕜 := ℝ) i) u
  filter_upwards [ae_all_iff.mpr h] with x hx
  simp_rw [hx]
  exact (PiLp.inner_apply _ _).symm

end Riesz1
