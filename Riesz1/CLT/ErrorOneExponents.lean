/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Exponent bookkeeping for Theorem 3

The bounds of Theorem 3 compare powers of the smoothing radius `δ = δ_N ∈ (0, 1]`.
For `0 < δ ≤ 1` the map `a ↦ δ^(-a)` is nondecreasing, so a larger exponent gives a larger
bound. This file records that monotonicity and the three exponent comparisons used in the
product bounds:

* `δ^(-(1 + α + η)) ≤ δ^(-(2 + α + τ))`, the bound on `‖ξ_reg'‖` times `‖ψ_reg‖`.
* `δ^(-(b + η)) δ^(-(1 + α + η)) ≤ δ^(-(2 + α + τ))` with `b = 1 - s + α`, the bound on
  `ψ_reg' ξ_reg'`.
* `δ^(-(2 + α + η)) ≤ δ^(-(2 + α + τ))`, the bound on `ψ_reg ξ_reg''`,

where `η = τ / 2`, `α < s/2` and `0 < s < 1`.
-/

@[expose] public section

noncomputable section

namespace Riesz1.Internal

/-- For a base `0 < δ ≤ 1`, the power `δ^(-a)` is nondecreasing in `a`. -/
lemma rpow_neg_le_rpow_neg_of_le {δ a b : ℝ} (h0 : 0 < δ) (h1 : δ ≤ 1) (hab : a ≤ b) :
    δ ^ (-a) ≤ δ ^ (-b) :=
  Real.rpow_le_rpow_of_exponent_ge h0 h1 (by linarith)

/-- The product exponent of the first bound: `1 + α + η ≤ 2 + α + τ` for `η = τ/2`. -/
lemma exponent_first_le {α τ : ℝ} (hτ : 0 < τ) :
    1 + α + τ / 2 ≤ 2 + α + τ := by
  linarith

/-- The exponent `(1 - s + α) + η + (1 + α + η)` of the product `ψ_reg' ξ_reg'` is at most
`2 + α + τ` when `η = τ/2`, because `α ≤ s` and `s < 1`. -/
lemma exponent_cross_le {α s τ : ℝ} (hα : α < s / 2) (hs0 : 0 < s) :
    (1 - s + α + τ / 2) + (1 + α + τ / 2) ≤ 2 + α + τ := by
  linarith

/-- The exponent of the second-derivative term `ψ_reg ξ_reg''`: `2 + α + η ≤ 2 + α + τ`. -/
lemma exponent_second_le {α τ : ℝ} (hτ : 0 < τ) :
    2 + α + τ / 2 ≤ 2 + α + τ := by
  linarith

/-- The square root of the variance bound of `plainSum` gives the power `K^(s/2 - 1 + τ)` in
equation (6.6): `K⁻¹ · (K^(s + 2τ))^(1/2) = K^(s/2 - 1 + τ)` for `K > 0`. -/
lemma inv_mul_sqrt_rpow {K s τ : ℝ} (hK : 0 < K) :
    K⁻¹ * (K ^ (s + 2 * τ)) ^ (1 / 2 : ℝ) = K ^ (s / 2 - 1 + τ) := by
  rw [← Real.rpow_neg_one, ← Real.rpow_mul hK.le, ← Real.rpow_add hK]
  congr 1
  ring

end Riesz1.Internal

end
end
