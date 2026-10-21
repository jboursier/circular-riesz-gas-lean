/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopCutoffInvariance
public import Riesz1.Frozen.Configuration

/-!
# Common rotation on the circle in ordered lift coordinates

The first label is retained under circle rotation. Every coordinate is shifted by the
same integer when the first lift crosses the seam of the fundamental region. In particular,
one must retain the cyclic ordering of the labels rather than sort the individual residues.
-/

@[expose] public section

noncomputable section

namespace Riesz1

/-- Circle rotation by `t`, in the fundamental region with the same first particle. -/
def loopRotate (N : ℕ+) (t : ℝ) (X : Configuration N) : Configuration N :=
  ⟨fun i => X.val i + (t - ⌊X.val ⟨0, N.pos⟩ + t⌋), by
    refine ⟨fun i j hij => by linarith [X.property.1 hij], ?_, ?_, ?_⟩
    · have h := Int.floor_le (X.val ⟨0, N.pos⟩ + t)
      linarith
    · have h := Int.lt_floor_add_one (X.val ⟨0, N.pos⟩ + t)
      linarith
    · intro i
      have h := X.property.2.2.2 i
      linarith⟩

/-- Every labelled circle coordinate is rotated by `t`, including across the seam. -/
theorem loopRotate_circle (N : ℕ+) (t : ℝ) (X : Configuration N) (i : Fin (N : ℕ)) :
    (((loopRotate N t X).val i : ℝ) : UnitAddCircle) = (X.val i : UnitAddCircle) + (t : UnitAddCircle) := by
  change ((X.val i + (t - (⌊X.val ⟨0, N.pos⟩ + t⌋ : ℝ)) : ℝ) : UnitAddCircle) = _
  rw [AddCircle.coe_add, AddCircle.coe_sub]
  simp

/-- The cutoff data part of Lemma 5.8: rotation invariance on the circle,
with the canonical ordered lifts and their cyclic particle labels. -/
theorem loopCutoff_rotate (s γ ε : ℝ) (N : ℕ+) (ℓ t : ℝ) (X : Configuration N) :
    loopCutoff s γ ε N ℓ (loopRotate N t X).val = loopCutoff s γ ε N ℓ X.val :=
  loopCutoff_add_const s γ ε N ℓ X.val (t - ⌊X.val ⟨0, N.pos⟩ + t⌋)

end Riesz1

end
