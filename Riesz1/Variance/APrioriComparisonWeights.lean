/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.Window
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The weights and affine comparator for a priori comparison

The paper's label one is the index zero. The
affine error uses the ordered anchored lift, so its reference coordinate
is the natural index of the label, including on the left side of the
cyclic window.
-/

@[expose] public section

noncomputable section

open Finset

namespace Riesz1

/-- The two comparison weights. -/
def comparisonWeight (N : ℕ+) (K s lam ε : ℝ) (i : Fin (N : ℕ)) : ℝ :=
  (if (labelDistToOne N i : ℝ) ≤ K ^ (1 + ε) then
    K ^ lam / (1 + (labelDistToOne N i : ℝ)) ^ (1 + lam) else 0) +
  (if K ^ (1 - ε) ≤ (labelDistToOne N i : ℝ) then
    K ^ (2 - s) / (1 + (labelDistToOne N i : ℝ)) ^ (3 - s) else 0)

/-- The augmented weights of the comparison part of Lemma 5.2. -/
def augmentedComparisonWeight (N : ℕ+) (K s lam ε : ℝ) (i : Fin (N : ℕ)) : ℝ :=
  comparisonWeight N K s lam ε i +
    K ^ lam / (1 + (labelDistToOne N i : ℝ)) ^ (1 + s / 2)

/-- The affine anchored comparator `G`. -/
def linearComparator (N : ℕ+) (K s lam ε : ℝ) (J : Finset (Fin (N : ℕ)))
    (y : Fin (N : ℕ) → ℝ) : ℝ :=
  ∑ i ∈ J, comparisonWeight N K s lam ε i * (((N : ℕ) : ℝ) * y i - (i : ℕ))

/-- The affine comparator for the augmented weights. -/
def augmentedLinearComparator (N : ℕ+) (K s lam ε : ℝ) (J : Finset (Fin (N : ℕ)))
    (y : Fin (N : ℕ) → ℝ) : ℝ :=
  ∑ i ∈ J, augmentedComparisonWeight N K s lam ε i *
    (((N : ℕ) : ℝ) * y i - (i : ℕ))

theorem comparisonWeight_nonneg {N : ℕ+} {K s lam ε : ℝ} (hK : 0 ≤ K)
    (i : Fin (N : ℕ)) : 0 ≤ comparisonWeight N K s lam ε i := by
  unfold comparisonWeight
  split_ifs <;> positivity

theorem augmentedComparisonWeight_nonneg {N : ℕ+} {K s lam ε : ℝ} (hK : 0 ≤ K)
    (i : Fin (N : ℕ)) : 0 ≤ augmentedComparisonWeight N K s lam ε i := by
  exact add_nonneg (comparisonWeight_nonneg hK i) (by positivity)

end Riesz1

end
