/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.BlockAverage
public import Riesz1.Rigidity.Gaps

/-!
# Deterministic identities for the rigidity of gaps

Part of the proof of Theorem 1. For every configuration `X`, every label
`i ∈ ℤ` and every scale `k`:

* the block length splits as `S_{i,k} - k = N (x_{i+k} - x_{i+k}^{[k]}) - N (x_i - x_i^{[k]}) + A_{i,k}`
  (equation (4.7)), where `S_{i,k} = blockLength X i k` and
  `A_{i,k} = centeredBlockDiff X i k`.
* for `k ≤ N`, the reflection `S_{i+k,N-k} - (N-k) = -(S_{i,k} - k)` holds, which follows from
  `x_{i+N} = x_i + 1`.
-/

@[expose] public section

noncomputable section

namespace Riesz1

variable {N : ℕ+}

/-- **Splitting of the block length** (equation (4.7)): the centered block length
`S_{i,k} - k` is the difference of the two block-average errors at `i + k` and `i`, plus the centered
block difference `A_{i,k}`. -/
theorem blockLength_sub_eq_split (X : Configuration N) (i : ℤ) (k : ℕ) :
    blockLength X i k - k =
      ((N : ℕ) : ℝ) * (cyclicLift X (i + k) - blockAverage X (i + k) k) -
        ((N : ℕ) : ℝ) * (cyclicLift X i - blockAverage X i k) + centeredBlockDiff X i k := by
  unfold blockLength centeredBlockDiff
  ring

/-- **Reflection of the block length**: for `k ≤ N`, the block of length `N - k` starting at `i + k`
has centered length equal to minus the centered length of the block of length `k` starting at `i`.
This uses `x_{i+N} = x_i + 1`. -/
theorem blockLength_reflect (X : Configuration N) (i : ℤ) {k : ℕ} (hkN : k ≤ (N : ℕ)) :
    blockLength X (i + k) ((N : ℕ) - k) - (((N : ℕ) - k : ℕ) : ℝ) = -(blockLength X i k - k) := by
  have hidx : i + (k : ℤ) + (((N : ℕ) - k : ℕ) : ℤ) = i + ((N : ℕ) : ℤ) := by omega
  unfold blockLength
  rw [hidx, cyclicLift_add_N, Nat.cast_sub hkN]
  ring

/-- The absolute centered block length is invariant under the reflection `k ↦ N - k`, `i ↦ i + k`. -/
theorem abs_blockLength_sub_reflect (X : Configuration N) (i : ℤ) {k : ℕ} (hkN : k ≤ (N : ℕ)) :
    |blockLength X i k - k| =
      |blockLength X (i + k) ((N : ℕ) - k) - (((N : ℕ) - k : ℕ) : ℝ)| := by
  rw [blockLength_reflect X i hkN, abs_neg]

end Riesz1

end
