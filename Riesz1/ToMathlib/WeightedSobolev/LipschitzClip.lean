/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Order.Filter.AtTopBot.Archimedean

/-!
# Clipping real functions to `[-R, R]`

For `R ≥ 0`, clipping a real number to `[-R, R]` does not increase its absolute value, it
is the identity on `[-R, R]`, and it is `1`-Lipschitz. Clipping a function along a Lipschitz map
keeps its Lipschitz constant on any set. These are the truncations used to remove the boundedness
hypothesis from the Herbst bound.
-/

public section

noncomputable section

open Set Filter Topology

namespace Riesz1.WeightedSobolev

/-- Clipping of a real number to the interval `[-R, R]`. -/
@[expose]
def clipReal (R r : ℝ) : ℝ := max (-R) (min R r)

/-- Clipping does not increase the absolute value when `0 ≤ R`. -/
theorem abs_clipReal_le {R r : ℝ} (hR : 0 ≤ R) : |clipReal R r| ≤ |r| := by
  unfold clipReal
  rw [abs_le]
  constructor
  · -- The lower bound: `min R r ≥ -|r|`, because `R ≥ 0 ≥ -|r|` and `r ≥ -|r|`.
    have hmin : -|r| ≤ min R r :=
      le_min ((neg_nonpos.mpr (abs_nonneg r)).trans hR) (neg_abs_le r)
    exact le_max_of_le_right hmin
  · -- The upper bound: both `-R ≤ |r|` and `min R r ≤ r ≤ |r|`.
    exact max_le ((neg_nonpos.mpr hR).trans (abs_nonneg r)) ((min_le_right R r).trans (le_abs_self r))

/-- Clipping at radius `R ≥ 0` takes values in `[-R, R]`. -/
theorem abs_clipReal_le_radius {R r : ℝ} (hR : 0 ≤ R) : |clipReal R r| ≤ R := by
  unfold clipReal
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left R r)⟩

/-- Clipping is the identity on `[-R, R]`. -/
theorem clipReal_eq_of_abs_le {R r : ℝ} (h : |r| ≤ R) : clipReal R r = r := by
  have hr := abs_le.mp h
  unfold clipReal
  rw [min_eq_right hr.2, max_eq_right hr.1]

/-- Clipping is `1`-Lipschitz on the real line. -/
theorem lipschitzWith_clipReal (R : ℝ) : LipschitzWith 1 (clipReal R) :=
  ((LipschitzWith.id).const_min R).const_max (-R)

/-- Clipping a function that is Lipschitz on a set keeps the same Lipschitz constant there. -/
theorem lipschitzOnWith_clipReal {E : Type*} [PseudoMetricSpace E] {K : NNReal} {s : Set E}
    {F : E → ℝ} (hF : LipschitzOnWith K F s) (R : ℝ) :
    LipschitzOnWith K (fun x => clipReal R (F x)) s := by
  have h := (lipschitzWith_clipReal R).comp_lipschitzOnWith hF
  rw [one_mul] at h
  exact h

/-- Clipping at level `n` eventually agrees with each real number, so the clipped values converge
to it along the natural numbers. -/
theorem tendsto_clipReal_nat (r : ℝ) :
    Tendsto (fun n : ℕ => clipReal (n : ℝ) r) atTop (𝓝 r) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop ⌈|r|⌉₊] with n hn
  refine (clipReal_eq_of_abs_le ?_).symm
  exact (Nat.le_ceil |r|).trans (Nat.cast_le.mpr hn)

end Riesz1.WeightedSobolev

end

end
