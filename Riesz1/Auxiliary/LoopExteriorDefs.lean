/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.LoopSizeBiasOffsets
public import Riesz1.Auxiliary.LoopArcsKernel
public import Riesz1.Auxiliary.LoopCutoffDefs

/-!
# The exterior event and its microscopic lifts

The objects that concern the exterior force. Integer labels
are offsets from the preceding particle, whose microscopic position is `-D`.
The exterior sum uses one cyclic period, with offsets in `(-N/2, N/2]`.
The force is defined only on the good-event carrier and the central interval.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

/-- The real microscopic lift `z_{J+j}` relative to the original origin. -/
def loopPrecedingLift {N : ℕ+} (X : LoopPrecedingConfiguration N) (j : ℤ) : ℝ :=
  (N : ℝ) * cyclicLift X.val (loopPrecedingLabel X + j)

/-- The good event, used in the partial-window regime. -/
def loopExteriorGood (N : ℕ+) (ℓ γ : ℝ) : Set (LoopPrecedingConfiguration N) :=
  {X | loopPrecedingD X ≤ gradM N ℓ γ / 8 ∧
    gradM N ℓ γ / 2 ≤ loopPrecedingLift X ⌊gradM N ℓ γ⌋ ∧
    loopPrecedingLift X (-⌊gradM N ℓ γ⌋) ≤ -gradM N ℓ γ / 2}

/-- Exterior offsets, represented once in `(-N/2, N/2]`, with the local window removed. -/
def loopExteriorLabels (N : ℕ+) (ℓ γ : ℝ) : Finset ℤ :=
  ((Finset.Icc (-(N : ℤ)) (N : ℤ)).filter
    (fun j => -(N : ℤ) < 2 * j ∧ 2 * j ≤ (N : ℤ))) \ gradLabels N ℓ γ

/-- A centered fundamental domain of the microscopic circle outside `[-M,M]`. -/
def loopExteriorBackground (N : ℕ+) (ℓ γ : ℝ) : Set ℝ :=
  Icc (-(N : ℝ) / 2) ((N : ℝ) / 2) \ Icc (-gradM N ℓ γ) (gradM N ℓ γ)

/-- The force, on its actual good-event and spatial carrier.
The background is the arclength integral on the centered fundamental domain. -/
def loopExteriorForce (s : ℝ) (N : ℕ+) (ℓ γ : ℝ)
    (X : {X : LoopPrecedingConfiguration N // X ∈ loopExteriorGood N ℓ γ})
    (z : Icc (-gradM N ℓ γ / 4) (gradM N ℓ γ / 4)) : ℝ :=
  (∑ j ∈ loopExteriorLabels N ℓ γ,
    deriv (loopArcG s N) (z.val - loopPrecedingLift X.val j)) -
      ∫ u in loopExteriorBackground N ℓ γ, deriv (loopArcG s N) (z.val - u)

theorem loopPrecedingLift_zero {N : ℕ+} (X : LoopPrecedingConfiguration N) :
    loopPrecedingLift X 0 = -loopPrecedingD X := by
  simp [loopPrecedingLift, loopPrecedingD]

theorem loopPrecedingLift_strictMono {N : ℕ+} (X : LoopPrecedingConfiguration N) :
    StrictMono (loopPrecedingLift X) := by
  intro i j hij
  exact mul_lt_mul_of_pos_left (cyclicLift_strictMono X.val (by omega))
    (by exact_mod_cast N.pos)

theorem loopPrecedingLift_add_N {N : ℕ+} (X : LoopPrecedingConfiguration N) (j : ℤ) :
    loopPrecedingLift X (j + N) = loopPrecedingLift X j + N := by
  simp only [loopPrecedingLift, ← add_assoc, cyclicLift_add_N]
  ring

theorem measurable_loopPrecedingLift (N : ℕ+) (j : ℤ) :
    Measurable (fun X : LoopPrecedingConfiguration N => loopPrecedingLift X j) := by
  have hm : Measurable (fun p : Configuration N × ℤ => cyclicLift p.1 p.2) :=
    measurable_from_prod_countable_left fun k => measurable_cyclicLift k
  exact (hm.comp (measurable_subtype_coe.prodMk
    ((measurable_loopPrecedingLabel N).add_const j))).const_mul _

theorem measurableSet_loopExteriorGood (N : ℕ+) (ℓ γ : ℝ) :
    MeasurableSet (loopExteriorGood N ℓ γ) := by
  exact ((measurableSet_le (measurable_loopPrecedingD N) measurable_const).inter
    ((measurableSet_le measurable_const (measurable_loopPrecedingLift N _)).inter
      (measurableSet_le (measurable_loopPrecedingLift N _) measurable_const)))

theorem measurableSet_loopExteriorBackground (N : ℕ+) (ℓ γ : ℝ) :
    MeasurableSet (loopExteriorBackground N ℓ γ) :=
  measurableSet_Icc.diff measurableSet_Icc

/-- The exterior lemma has no two-particle instance under its scale assumptions. -/
theorem not_gradPartial_two {N : ℕ+} (hN : (N : ℕ) = 2) {ℓ γ : ℝ}
    (hK : 1 ≤ (N : ℝ) * ℓ) (hγ : 0 ≤ γ) : ¬GradPartial N ℓ γ := by
  have hM : 1 ≤ gradM N ℓ γ := Real.one_le_rpow hK hγ
  have hNr : (N : ℝ) = 2 := by exact_mod_cast hN
  change ¬gradM N ℓ γ < (N : ℝ) / 8
  rw [hNr]
  linarith

end Riesz1

end
