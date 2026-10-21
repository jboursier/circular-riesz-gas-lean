/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Round

/-!
# Circular distance

The distance `circDist L y = |y - L · round(y/L)|` from `y` to `L ℤ`, the
absolute value of the representative of `y` in `[-L/2, L/2]`, with its basic geometry. It is shared
by the regularization and the gradient-splitting arguments.
-/

public section

namespace Riesz1

/-- The distance from `y` to `L ℤ`: the absolute value of the representative of `y` in
`[-L/2, L/2]`. -/
@[expose] noncomputable def circDist (L y : ℝ) : ℝ :=
  |y - L * round (y / L)|

section Distance

lemma circDist_nonneg (L y : ℝ) : 0 ≤ circDist L y := abs_nonneg _

/-- The distance to `L ℤ` is at most the distance to any multiple `k L`. -/
lemma circDist_le_abs_sub {L : ℝ} (hL : 0 < L) (y : ℝ) (k : ℤ) :
    circDist L y ≤ |y - L * k| := by
  unfold circDist
  have h1 := round_le (y / L) k
  have e : ∀ z : ℝ, |y - L * z| = L * |y / L - z| := fun z => by
    rw [show y - L * z = L * (y / L - z) by field_simp, abs_mul, abs_of_pos hL]
  rw [e, e]
  exact mul_le_mul_of_nonneg_left h1 hL.le

/-- The distance to `L ℤ` is invariant under translation by a multiple of `L`. -/
lemma circDist_add_int_mul {L : ℝ} (hL : 0 < L) (y : ℝ) (k : ℤ) :
    circDist L (y + k * L) = circDist L y := by
  unfold circDist
  have e : (y + k * L) / L = y / L + k := by field_simp
  rw [e, round_add_intCast]
  congr 1
  push_cast
  ring

/-- The distance to `L ℤ` is `1`-Lipschitz for the line metric. -/
lemma circDist_le_add_abs {L : ℝ} (hL : 0 < L) (y z : ℝ) :
    circDist L y ≤ circDist L z + |y - z| := by
  have h1 := circDist_le_abs_sub hL y (round (z / L))
  have h2 : |y - L * round (z / L)| ≤ |y - z| + |z - L * round (z / L)| := abs_sub_le y z _
  have h3 : circDist L z = |z - L * round (z / L)| := rfl
  linarith

/-- On the half-period interval, the distance to `L ℤ` is the absolute value. -/
lemma circDist_eq_abs {L y : ℝ} (hL : 0 < L) (hy : |y| ≤ L / 2) : circDist L y = |y| := by
  refine le_antisymm ?_ ?_
  · simpa using circDist_le_abs_sub hL y 0
  · unfold circDist
    have ht : |y / L| ≤ 1 / 2 := by
      rw [abs_div, abs_of_pos hL, div_le_iff₀ hL]
      linarith
    have e : |y - L * round (y / L)| = L * |y / L - round (y / L)| := by
      rw [show y - L * round (y / L) = L * (y / L - round (y / L)) by field_simp,
        abs_mul, abs_of_pos hL]
    have hy' : |y| = L * |y / L| := by
      rw [abs_div, abs_of_pos hL]
      field_simp
    rw [e, hy']
    apply mul_le_mul_of_nonneg_left _ hL.le
    by_cases h0 : round (y / L) = 0
    · rw [h0]
      simp
    · have h1 : (1 : ℝ) ≤ |(round (y / L) : ℝ)| := by
        have : (1 : ℤ) ≤ |round (y / L)| := Int.one_le_abs h0
        exact_mod_cast this
      have h2 := abs_sub_abs_le_abs_sub ((round (y / L) : ℤ) : ℝ) (y / L)
      rw [abs_sub_comm] at h2
      linarith

end Distance

end Riesz1

end
