/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.Calculus.PowerSumFromPoint

/-!
# Finite power tails above a real radius

The integral-test bound for integer power sums, with a real lower
threshold. The estimate is uniform over the finite set being summed.
-/

public section

noncomputable section

open Finset

namespace Riesz1

/-- A power tail above a real radius, with no upper endpoint needed. -/
theorem sum_natCast_rpow_neg_le_of_real_ge {p R : ℝ} (hp : 1 < p) (hR : 1 ≤ R)
    (S : Finset ℕ) (hS : ∀ j ∈ S, R ≤ (j : ℝ)) :
    ∑ j ∈ S, (j : ℝ) ^ (-p) ≤ (1 + 1 / (p - 1)) * R ^ (1 - p) := by
  have hJ : 1 ≤ ⌈R⌉₊ := by
    exact_mod_cast hR.trans (Nat.le_ceil R)
  apply (sum_natCast_rpow_neg_le_of_ge hp hJ S (fun j hj => Nat.ceil_le.mpr (hS j hj))).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.rpow_le_rpow_of_nonpos (by linarith) (Nat.le_ceil R) (by linarith)

end Riesz1

end
