/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Gibbs.AnchoredCoordinates
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# The anchored coordinate change has determinant one

The coordinate change `(x_1, y) ↦ (x_1, x_1 + y_2, …, x_1 + y_N)` has
determinant one. Its inverse is the anchor map `x ↦ (x_1, x_2 - x_1, …, x_N - x_1)`, which is linear
on `Fin (n + 1) → ℝ` and lower triangular with unit diagonal in the standard basis. The determinant
of the coordinate change is the inverse of this determinant, hence also one.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Matrix

namespace Riesz1

variable {n : ℕ}

/-- The anchor map `x ↦ (x_0, x_1 - x_0, …, x_n - x_0)` as a linear endomorphism of
`Fin (n + 1) → ℝ`. Its inverse is the anchored coordinate change. -/
def anchorChange (n : ℕ) : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ) where
  toFun x := Fin.cons (x 0) (fun j : Fin n => x j.succ - x 0)
  map_add' x y := by
    ext i
    induction i using Fin.cases with
    | zero => simp
    | succ j => simp; ring
  map_smul' a x := by
    ext i
    induction i using Fin.cases with
    | zero => simp
    | succ j => simp; ring

theorem anchorChange_zero (x : Fin (n + 1) → ℝ) : anchorChange n x 0 = x 0 := by
  simp [anchorChange]

theorem anchorChange_succ (x : Fin (n + 1) → ℝ) (j : Fin n) :
    anchorChange n x j.succ = x j.succ - x 0 := by
  simp [anchorChange]

/-- In the standard basis, the anchor map is lower triangular: its only nonzero entries lie on or
below the diagonal. -/
theorem anchorChange_matrix_isLowerTriangular :
    (LinearMap.toMatrix' (anchorChange n)).IsLowerTriangular := by
  intro i j hij
  rw [OrderDual.toDual_lt_toDual] at hij
  simp only [LinearMap.toMatrix'_apply]
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => exact absurd hij (lt_irrefl _)
    | succ k =>
      rw [anchorChange_zero]
      simp
  | succ l =>
    induction j using Fin.cases with
    | zero => exact (Fin.not_lt_zero _ hij).elim
    | succ k =>
      rw [anchorChange_succ]
      have hlk : l ≠ k := by
        intro h
        subst h
        exact lt_irrefl _ (Fin.succ_lt_succ_iff.mp hij)
      simp [hlk]

/-- The anchor map has determinant one. -/
theorem det_anchorChange : LinearMap.det (anchorChange n) = 1 := by
  rw [← LinearMap.det_toMatrix', Matrix.det_of_isLowerTriangular _
    anchorChange_matrix_isLowerTriangular]
  rw [Fin.prod_univ_succ]
  simp only [LinearMap.toMatrix'_apply]
  rw [anchorChange_zero]
  simp only [Pi.single_apply]
  simp [anchorChange_succ]

end Riesz1

end
end
