/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.AuxiliaryReductionRates

/-!
# Endpoint losses in the two auxiliary family estimates

Proposition 5.6: increasing the transport exponent slightly
costs an arbitrarily small power, uniformly for every microscopic length.
-/

public section

namespace Riesz1.Internal

/-- Absorb a permitted transport-exponent increase in both the derivative
variance rate and the energy rate, including the critical energy power. -/
theorem auxiliary_family_increased_rates {K s α δ ε : ℝ}
    (hK : 1 ≤ K) (hδ : 2 * δ ≤ ε / 2) (hε : 0 ≤ ε) :
    (K ^ (ε / 2) * (K ^ s + K ^ (2 * (1 - s + (α + δ)))) ≤
      K ^ ε * (K ^ s + K ^ (2 * (1 - s + α)))) ∧
    (K ^ (ε / 2) * (1 + K ^ (2 * (1 - s + (α + δ)) - 1)) ≤
      K ^ ε * (1 + K ^ (2 * (1 - s + α) - 1))) := by
  have hK0 : 0 < K := by linarith
  constructor
  · simp only [mul_add, ← Real.rpow_add hK0]
    exact add_le_add (Real.rpow_le_rpow_of_exponent_le hK (by linarith))
      (Real.rpow_le_rpow_of_exponent_le hK (by linarith))
  · simp only [mul_add, mul_one, ← Real.rpow_add hK0]
    exact add_le_add (Real.rpow_le_rpow_of_exponent_le hK (by linarith))
      (Real.rpow_le_rpow_of_exponent_le hK (by linarith))

end Riesz1.Internal
