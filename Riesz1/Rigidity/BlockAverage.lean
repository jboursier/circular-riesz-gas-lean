/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.BlockAverageRepresentatives
public import Riesz1.Rigidity.Gaps

/-!
# Block averages of cyclic lifts and centered block differences

For a configuration `X` of `N` particles, a label `i`, and a
scale `k`, the block average `x_i^{[k]}` is the mean of the cyclic lifts `x_j = cyclicLift X j` over
the representatives `J_k(i)` of `Riesz1.cyclicRep`. Since the representatives are integers, the average
is a function of the lifts. Its shift law `x_{i+N}^{[k]} = x_i^{[k]} + 1` is `blockAverage_add_N`.

The centered block difference `A_{i,k} = N (x_{i+k}^{[k]} - x_i^{[k]}) - k` is
`Riesz1.centeredBlockDiff`. Both are measurable functions of the configuration.
-/

@[expose] public section

open MeasureTheory Finset

namespace Riesz1

variable {N : ℕ+}

/-! ### Block averages -/

/-- The block average `x_i^{[k]} = |J_k(i)|^{-1} ∑_{j ∈ J_k(i)} x_j`, with
the cyclic lifts `x_j = cyclicLift X j` of the configuration `X`. -/
noncomputable def blockAverage (X : Configuration N) (i : ℤ) (k : ℕ) : ℝ :=
  ((cyclicRep N k i).card : ℝ)⁻¹ * ∑ j ∈ cyclicRep N k i, cyclicLift X j

/-- At scale zero the block is the single label `{i}`, so the average is the lift `x_i`. -/
theorem blockAverage_zero (X : Configuration N) (i : ℤ) :
    blockAverage X i 0 = cyclicLift X i := by
  have hN : 2 * 0 < (N : ℕ) := by simp
  have hrep : cyclicRep N 0 i = {i} := by
    unfold cyclicRep
    simp only [hN, ↓reduceIte, Nat.cast_zero, sub_zero, add_zero, Finset.Icc_self]
  simp [blockAverage, hrep]

/-- Moving the label by `N` moves the block average by one: `x_{i+N}^{[k]} = x_i^{[k]} + 1`. -/
theorem blockAverage_add_N (X : Configuration N) (i : ℤ) {k : ℕ} (hk : 1 ≤ k) :
    blockAverage X (i + ((N : ℕ) : ℤ)) k = blockAverage X i k + 1 := by
  have hcard : ((cyclicRep N k i).card : ℝ) ≠ 0 := by
    exact_mod_cast (cyclicRep_card_pos hk i).ne'
  unfold blockAverage
  rw [cyclicRep_add_N, card_map, sum_map]
  simp only [addRightEmbedding_apply, cyclicLift_add_N, sum_add_distrib, sum_const, nsmul_eq_mul,
    mul_one]
  rw [mul_add, inv_mul_cancel₀ hcard]

/-- A block average is a measurable function of the configuration. -/
theorem measurable_blockAverage (i : ℤ) (k : ℕ) :
    Measurable fun X : Configuration N => blockAverage X i k := by
  unfold blockAverage
  exact measurable_const.mul (Finset.measurable_sum _ fun j _ => measurable_cyclicLift j)

/-! ### Centered block differences -/

/-- The centered block difference `A_{i,k} = N (x_{i+k}^{[k]} - x_i^{[k]}) - k`. -/
noncomputable def centeredBlockDiff (X : Configuration N) (i : ℤ) (k : ℕ) : ℝ :=
  ((N : ℕ) : ℝ) * (blockAverage X (i + k) k - blockAverage X i k) - k

/-- The centered block difference is a measurable function of the configuration. -/
theorem measurable_centeredBlockDiff (i : ℤ) (k : ℕ) :
    Measurable fun X : Configuration N => centeredBlockDiff X i k := by
  unfold centeredBlockDiff
  exact (((measurable_blockAverage _ _).sub (measurable_blockAverage _ _)).const_mul _).sub
    measurable_const

end Riesz1

end
