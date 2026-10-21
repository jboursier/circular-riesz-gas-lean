/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic

/-!
# Divergence of the sine-squared harmonic series

The sine addition formula bounds the sum of two consecutive squared sines below.
This proves divergence without a separate conditional convergence argument for cosines.
-/

public section

namespace Riesz1

/-- Two consecutive phases cannot both have small sine if their difference has nonzero sine. -/
lemma sin_sq_le_two_mul_adjacent (θ x : ℝ) :
    Real.sin θ ^ 2 ≤ 2 * (Real.sin x ^ 2 + Real.sin (x + θ) ^ 2) := by
  have he : Real.sin θ = Real.sin (x + θ) * Real.cos x -
      Real.cos (x + θ) * Real.sin x := by
    rw [← Real.sin_sub]
    congr 1
    ring
  have h1 : (Real.sin (x + θ) * Real.cos x) ^ 2 ≤ Real.sin (x + θ) ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg (Real.sin (x + θ)))
      (sub_nonneg.mpr (Real.cos_sq_le_one x))]
  have h2 : (Real.cos (x + θ) * Real.sin x) ^ 2 ≤ Real.sin x ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg (Real.sin x))
      (sub_nonneg.mpr (Real.cos_sq_le_one (x + θ)))]
  rw [he]
  nlinarith [sq_nonneg (Real.sin (x + θ) * Real.cos x +
    Real.cos (x + θ) * Real.sin x)]

/-- The sine-squared harmonic series diverges for every phase not a multiple of π. -/
theorem not_summable_sin_sq_div_nat_add_one {θ : ℝ} (hθ : Real.sin θ ≠ 0) :
    ¬ Summable (fun n : ℕ => Real.sin ((n : ℝ) * θ) ^ 2 / ((n : ℝ) + 1)) := by
  intro hs
  have htail : Summable (fun n : ℕ =>
      Real.sin (((n : ℝ) + 1) * θ) ^ 2 / ((n : ℝ) + 2)) := by
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using
      (summable_nat_add_iff 1).mpr hs
  have hshift : Summable (fun n : ℕ =>
      Real.sin (((n : ℝ) + 1) * θ) ^ 2 / ((n : ℝ) + 1)) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      (htail.mul_left 2)
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (Real.sin (((n : ℝ) + 1) * θ))]
  have hconst : Summable (fun n : ℕ => Real.sin θ ^ 2 / ((n : ℝ) + 1)) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      ((hs.add hshift).mul_left 2)
    rw [← add_div, ← mul_div_assoc, div_le_div_iff_of_pos_right (by positivity)]
    simpa only [add_mul, one_mul] using sin_sq_le_two_mul_adjacent θ ((n : ℝ) * θ)
  have hh : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
    convert hconst.mul_left (Real.sin θ ^ 2)⁻¹ using 1
    funext n
    field_simp
  have hh' : Summable (fun n : ℕ => (1 : ℝ) / n) :=
    (summable_nat_add_iff 1).mp (by simpa using hh)
  exact Real.not_summable_one_div_natCast hh'

end Riesz1
