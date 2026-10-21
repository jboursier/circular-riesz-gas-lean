/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.VarAlSingularField

/-!
# Two-particle checks for singular-field comparison

At `N = 2`, `ℓ = 1/2`, the cutoff is identically zero on the physical
domain. Each selected edge has the two complementary factors
`c(2g)` and `c(2/g)`, one of which vanishes for every positive gap `g`.
This checks the boundary `K = 1`, where a scale-dependent loss cannot
absorb a fixed numerical factor by increasing its exponent.
-/

@[expose] public section

noncomputable section

open Finset

namespace Riesz1

/-- The edge cutoff vanishes at unit scale for every positive gap. -/
theorem varAlSingular_edge_cutoff_unit {g : ℝ} (hg : 0 < g) :
    cutoffC (2 * g) * cutoffC (2 / g) = 0 := by
  have hz : ∀ r : ℝ, 2 ≤ r → cutoffC r = 0 := by
    intro r hr
    unfold cutoffC
    rw [max_eq_left (by linarith), min_eq_right zero_le_one]
  by_cases h : 1 ≤ g
  · rw [hz _ (by linarith), zero_mul]
  · have hdiv : 2 ≤ 2 / g := by
      rw [le_div_iff₀ hg]
      linarith
    rw [hz _ hdiv, mul_zero]

/-- Two particles at the smallest allowed scale have a vanishing cutoff. -/
theorem varAlSingular_cutoff_two_unitScale (s γ ε : ℝ) (X : Fin (2 : ℕ) → ℝ)
    (hX : X ∈ orderedDomain (2 : ℕ+)) :
    loopCutoff s γ ε (2 : ℕ+) (1 / 2) X = 0 := by
  have hfull : ¬GradPartial (2 : ℕ+) (1 / 2) (2 * γ) := by
    norm_num [GradPartial, gradM]
  have hK : 1 ≤ ((2 : ℕ+) : ℝ) * (1 / 2) := by norm_num
  have hg : 0 < (2 : ℝ) * (gradLift (2 : ℕ+) X 1 - gradLift (2 : ℕ+) X 0) := by
    have hm := hX.1 (show (0 : Fin 2) < 1 by norm_num)
    norm_num [gradLift, gradIndex]
    exact hm
  unfold loopCutoff
  have hprod : (∏ i ∈ gradLabels (2 : ℕ+) (1 / 2) (2 * γ),
      if gradInWindow (2 : ℕ+) (1 / 2) (2 * γ) (i + 1) then
        cutoffC (2 * ((2 : ℝ) * (gradLift (2 : ℕ+) X (i + 1) - gradLift (2 : ℕ+) X i)) /
          (((2 : ℝ) * (1 / 2)) ^ ε)) *
        cutoffC (2 / ((((2 : ℝ) * (1 / 2)) ^ ε) *
          ((2 : ℝ) * (gradLift (2 : ℕ+) X (i + 1) - gradLift (2 : ℕ+) X i)))) else 1) = 0 := by
    apply Finset.prod_eq_zero (varAlSingular_zero_mem (2 : ℕ+) (1 / 2) (2 * γ) hK)
    simp only [gradInWindow, hfull, false_implies, ↓reduceIte, zero_add]
    norm_num only [mul_one_div_cancel, Real.one_rpow, div_one, one_mul]
    exact varAlSingular_edge_cutoff_unit hg
  exact mul_eq_zero.mpr (Or.inr hprod)

end Riesz1

end
