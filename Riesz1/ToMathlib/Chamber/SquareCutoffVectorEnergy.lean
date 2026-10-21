/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.Chamber.SquareCutoffEnergy

/-!
# Square partition cancellation for a full gradient

The scalar cancellation, summed over a finite orthonormal basis, with
one potential term. Used on the quotient.
-/

@[expose] public section

noncomputable section

open scoped ComplexInnerProductSpace

namespace Riesz1.Internal

/-- Full finite-dimensional energy residual under a square partition weight. -/
theorem square_cutoff_vector_energy_residual {ι : Type*} [Fintype ι]
    (r dr b V : ℝ) (db w : ι → ℝ) (u : ℂ) (g : ι → ℂ) :
    (∑ i, ‖(r * db i + dr * w i * b) • u + (r * b) • g i‖ ^ 2) +
        V * ‖(r * b) • u‖ ^ 2 - (∑ i, (r * db i + dr * w i * b) ^ 2) * ‖u‖ ^ 2 =
      r ^ 2 * ((∑ i, ‖db i • u + b • g i‖ ^ 2) + V * ‖b • u‖ ^ 2 -
        (∑ i, db i ^ 2) * ‖u‖ ^ 2) +
      (r * dr) * (∑ i, 2 * b ^ 2 * w i * RCLike.re (⟪u, g i⟫ : ℂ)) := by
  classical
  have h (i : ι) := square_cutoff_energy_residual r (dr * w i) b (db i) 0 u (g i)
  simp only [zero_mul, add_zero] at h
  calc
    _ = (∑ i, (‖(r * db i + dr * w i * b) • u + (r * b) • g i‖ ^ 2 -
        (r * db i + dr * w i * b) ^ 2 * ‖u‖ ^ 2)) + V * ‖(r * b) • u‖ ^ 2 := by
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
      ring
    _ = (∑ i, (r ^ 2 * (‖db i • u + b • g i‖ ^ 2 - db i ^ 2 * ‖u‖ ^ 2) +
        (r * (dr * w i)) * (2 * b ^ 2 * RCLike.re (⟪u, g i⟫ : ℂ)))) +
        V * ‖(r * b) • u‖ ^ 2 := by simp_rw [h]
    _ = _ := by
      have hmix : (∑ i, (r * (dr * w i)) *
          (2 * b ^ 2 * RCLike.re (⟪u, g i⟫ : ℂ))) =
          (r * dr) * (∑ i, 2 * b ^ 2 * w i * RCLike.re (⟪u, g i⟫ : ℂ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [Finset.sum_add_distrib, hmix, ← Finset.mul_sum,
        Finset.sum_sub_distrib, ← Finset.sum_mul]
      simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      ring

end Riesz1.Internal
