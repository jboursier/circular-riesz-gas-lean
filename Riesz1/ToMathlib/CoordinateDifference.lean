/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic

/-!
# Differences of sums of distinct Euclidean coordinates

Each sum over `m` distinct coordinates has operator norm at most `√m`.
Thus a difference of two such sums has norm at most `2√m`, even when
the two coordinate sets overlap.
-/

@[expose] public section

noncomputable section

open Finset

namespace Riesz1.Internal

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Difference of the two indicated coordinate sums, as a linear functional. -/
def coordinateDifference (f g : ι → κ) : EuclideanSpace ℝ κ →L[ℝ] ℝ :=
  (∑ r, EuclideanSpace.proj (g r)) - ∑ r, EuclideanSpace.proj (f r)

omit [Fintype κ] in
theorem coordinateDifference_apply (f g : ι → κ) (x : EuclideanSpace ℝ κ) :
    coordinateDifference f g x = (∑ r, x (g r)) - ∑ r, x (f r) := by
  simp [coordinateDifference]

/-- Cauchy--Schwarz for any injectively selected set of coordinates. -/
theorem abs_sum_coordinates_le (f : ι → κ) (hf : Function.Injective f)
    (x : EuclideanSpace ℝ κ) :
    |∑ r, x (f r)| ≤ Real.sqrt (Fintype.card ι) * ‖x‖ := by
  classical
  have hsq : (∑ r, x (f r)) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ r, x (f r) ^ 2 := by
    simpa using (sq_sum_le_card_mul_sum_sq (s := (univ : Finset ι)) (f := fun r => x (f r)))
  have hsub : ∑ r, x (f r) ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    have he : (∑ r, x (f r) ^ 2) = ∑ j ∈ univ.image f, x j ^ 2 := by
      exact (Finset.sum_image (f := fun j => x j ^ 2) (fun a _ b _ hab => hf hab)).symm
    rw [he]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun j _ _ => sq_nonneg (x j))
  have hroot := Real.sq_sqrt (Nat.cast_nonneg (Fintype.card ι) : (0 : ℝ) ≤ _)
  have hbound : (∑ r, x (f r)) ^ 2 ≤ (Real.sqrt (Fintype.card ι) * ‖x‖) ^ 2 := by
    calc (∑ r, x (f r)) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ r, x (f r) ^ 2 := hsq
      _ ≤ (Fintype.card ι : ℝ) * ‖x‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hsub (Nat.cast_nonneg _)
      _ = _ := by rw [mul_pow, hroot]
  exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp (by simpa only [sq_abs] using hbound)

/-- Overlap between the two selected coordinate sets requires no disjointness
hypothesis and does not worsen this bound. -/
theorem norm_coordinateDifference_le (f g : ι → κ)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ‖coordinateDifference f g‖ ≤ 2 * Real.sqrt (Fintype.card ι) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  rw [coordinateDifference_apply, Real.norm_eq_abs]
  calc |(∑ r, x (g r)) - ∑ r, x (f r)| ≤
        |∑ r, x (g r)| + |∑ r, x (f r)| := abs_sub _ _
    _ ≤ Real.sqrt (Fintype.card ι) * ‖x‖ + Real.sqrt (Fintype.card ι) * ‖x‖ :=
      add_le_add (abs_sum_coordinates_le g hg x) (abs_sum_coordinates_le f hf x)
    _ = _ := by ring

/-- Reindex a sum over consecutive integer labels by a finite type. -/
theorem sum_integer_block {A : Type*} [AddCommMonoid A]
    (i : ℤ) (L : ℕ) (f : ℤ → A) :
    (∑ r : Fin (L + 1), f (i + r.val)) = ∑ j ∈ Icc i (i + L), f j := by
  apply sum_bij (fun (r : Fin (L + 1)) _ => i + (r.val : ℤ))
  · intro r _
    have := r.isLt
    simp only [mem_Icc]
    omega
  · intro r _ s _ h
    apply Fin.ext
    omega
  · intro j hj
    simp only [mem_Icc] at hj
    refine ⟨⟨(j - i).toNat, by omega⟩, mem_univ _, ?_⟩
    dsimp
    omega
  · intro r _
    rfl

end Riesz1.Internal

end
