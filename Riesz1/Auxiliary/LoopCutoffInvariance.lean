/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopCutoffDefs

/-!
# Invariance of the anchored cutoff under a common shift

The cutoff data part of Lemma 5.8: the cutoff `η` is invariant under a common rotation.
The cutoff is a product of functions of the lifted differences `x_j - x_i` and of the gaps, and a
common shift `X ↦ X + c` of all coordinates leaves those differences unchanged. Thus `η` is
invariant under the shift `X ↦ X + c` for every real `c`, as a total formula on `ℝ^N`.
-/

@[expose] public section

namespace Riesz1

noncomputable section

/-- A common shift of the coordinates shifts every lift by the same amount. -/
lemma gradLift_add_const (N : ℕ+) (X : Fin (N : ℕ) → ℝ) (c : ℝ) (j : ℤ) :
    gradLift N (fun i => X i + c) j = gradLift N X j + c := by
  unfold gradLift
  ring

/-- The anchored cutoff `η` is invariant under a common shift `X ↦ X + c` of all coordinates. -/
lemma loopCutoff_add_const (s γ ε : ℝ) (N : ℕ+) (ℓ : ℝ) (X : Fin (N : ℕ) → ℝ) (c : ℝ) :
    loopCutoff s γ ε N ℓ (fun i => X i + c) = loopCutoff s γ ε N ℓ X := by
  unfold loopCutoff
  simp only [gradLift_add_const, add_sub_add_right_eq_sub]

end

end Riesz1

end
