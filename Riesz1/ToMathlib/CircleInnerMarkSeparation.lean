/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.CircleCoeffUniqueness

/-!
# Uniform separation of points in a fixed inner interval

Finitely many distinct real points in `[-r,r]`, with `r<1/2`, remain
uniformly separated on every circle of length at least one. The support
margin controls possible wraparound, independently of the period.
-/

public section

namespace Riesz1

/-- A fixed inner interval prevents distinct marks from approaching
each other through a varying circle's antipodal cut. The statement
also includes an empty or singleton marked family. -/
theorem exists_uniform_circle_separation_of_inner
    {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : Function.Injective a)
    {r : ℝ} (hr : r < 1/2) (har : ∀ i, |a i| ≤ r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (L : ℝ), 1 ≤ L →
      ∀ i j, i ≠ j → δ ≤ dist (a i : AddCircle L) (a j : AddCircle L) := by
  obtain ⟨d, hd, hsep⟩ := exists_pos_le_dist_of_injective ha
  refine ⟨min d (1-2*r), lt_min hd (by linarith), fun L hL i j hij => ?_⟩
  have hL0 : 0 < L := by linarith
  rw [dist_coe_eq_circDist_sub hL0]
  unfold circDist
  let k := round ((a i-a j)/L)
  change min d (1-2*r) ≤ |a i-a j-L*(k : ℝ)|
  by_cases hk : k = 0
  · simp only [hk, Int.cast_zero, mul_zero, sub_zero]
    exact (min_le_left _ _).trans (by simpa only [Real.dist_eq] using hsep i j hij)
  · have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk
    have hkL : L ≤ |L*(k : ℝ)| := by rw [abs_mul, abs_of_pos hL0]; nlinarith
    have hab : |a i-a j| ≤ 2*r := (abs_sub _ _).trans (by linarith [har i, har j])
    have ht := abs_sub_abs_le_abs_sub (L*(k : ℝ)) (a i-a j)
    rw [abs_sub_comm (L*(k : ℝ))] at ht
    exact (min_le_right _ _).trans (by linarith)

end Riesz1
