/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.PositiveRadiusPartition

/-!
# Value bounds for normalized radius partitions

The normalized partition preserves the absolute value of its input and
turns a sum of radius power bounds into one radius bound for each piece.
These estimates require no separation of the radii's centers.
-/

public section

open scoped BigOperators

namespace Riesz1

/-- Each normalized piece is pointwise dominated by its input. -/
theorem abs_positive_radii_partition_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (d : ι → ℝ) (hd : ∀ j, 0 < d j) (f b : ℝ) (j : ι) :
    |f * d j ^ (-1 - b) / (∑ k, d k ^ (-1 - b))| ≤ |f| := by
  classical
  have hp (k : ι) : 0 < d k ^ (-1 - b) := Real.rpow_pos_of_pos (hd k) _
  have hS : 0 < ∑ k, d k ^ (-1 - b) :=
    Finset.sum_pos (fun k _ => hp k) Finset.univ_nonempty
  rw [abs_div, abs_mul, abs_of_pos (hp j), abs_of_pos hS]
  apply (div_le_iff₀ hS).mpr
  exact mul_le_mul_of_nonneg_left
    (Finset.single_le_sum (fun k _ => (hp k).le) (Finset.mem_univ j)) (abs_nonneg f)

/-- The value of a normalized piece satisfies the corresponding
single-radius power bound, with only a cardinality loss. -/
theorem positive_radii_partition_value_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    (d : ι → ℝ) (hd : ∀ j, 0 < d j) {f A b : ℝ}
    (hA : 0 ≤ A) (hb : 0 ≤ b) (hf : |f| ≤ A * ∑ k, d k ^ (-b)) (j : ι) :
    |f * d j ^ (-1 - b) / (∑ k, d k ^ (-1 - b))| ≤
      A * (Fintype.card ι : ℝ) * d j ^ (-b) := by
  classical
  obtain ⟨i, hi, hmin⟩ := positive_radii_minimum d hd
  have hp (k : ι) : 0 < d k ^ (-1 - b) := Real.rpow_pos_of_pos (hd k) _
  have hS : 0 < ∑ k, d k ^ (-1 - b) :=
    Finset.sum_pos (fun k _ => hp k) Finset.univ_nonempty
  have hfv : |f| ≤ A * (Fintype.card ι : ℝ) * d i * ∑ k, d k ^ (-1 - b) := by
    exact hf.trans (by
      have hh := mul_le_mul_of_nonneg_left (positive_radii_power_sum d hd hb i hmin) hA
      simpa only [mul_assoc] using hh)
  rw [abs_div, abs_mul, abs_of_pos (hp j), abs_of_pos hS]
  calc
    _ ≤ (A * (Fintype.card ι : ℝ) * d i * ∑ k, d k ^ (-1 - b)) *
        d j ^ (-1 - b) / (∑ k, d k ^ (-1 - b)) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hfv (hp j).le) hS.le
    _ = A * (Fintype.card ι : ℝ) * d i * d j ^ (-1 - b) := by field_simp
    _ ≤ A * (Fintype.card ι : ℝ) * d j * d j ^ (-1 - b) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hmin j) (mul_nonneg hA (Nat.cast_nonneg _))) (hp j).le
    _ = _ := by
      have he : d j * d j ^ (-1 - b) = d j ^ (-b) := by
        calc
          _ = d j ^ (1 : ℝ) * d j ^ (-1 - b) := by rw [Real.rpow_one]
          _ = d j ^ ((1 : ℝ) + (-1 - b)) := (Real.rpow_add (hd j) _ _).symm
          _ = _ := by congr 1; ring
      rw [mul_assoc, he]

end Riesz1
