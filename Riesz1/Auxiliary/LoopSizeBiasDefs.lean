/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Rigidity.BoundarySelectionLawBounds
public import Riesz1.Gibbs.AnchoredCoordinates

/-!
# Preceding-particle coordinates

Coordinates are defined on precisely the configurations without a
particle at zero. There are no assigned values on the excluded null set. The integer label
uses the canonical preceding label already constructed for count inversion.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace Riesz1

/-- Configurations without a particle at zero. All integer lifts are included. -/
def loopPrecedingDomain (N : ℕ+) : Set (Configuration N) :=
  {X | ∀ j : ℤ, cyclicLift X j ≠ 0}

/-- The carrier of the preceding-particle variables. -/
@[reducible] def LoopPrecedingConfiguration (N : ℕ+) := {X : Configuration N // X ∈ loopPrecedingDomain N}

/-- The integer label of the particle just before zero. -/
def loopPrecedingLabel {N : ℕ+} (X : LoopPrecedingConfiguration N) : ℤ :=
  precedingLabel 0 0 X.val

/-- The microscopic displacement `D = -N x_J` from the preceding particle to zero. -/
def loopPrecedingD {N : ℕ+} (X : LoopPrecedingConfiguration N) : ℝ :=
  -(N : ℝ) * cyclicLift X.val (loopPrecedingLabel X)

/-- The anchored vector, including its zero coordinate, after the preceding particle is
relabeled zero. This is the full-carrier formula `y_i = x_{J+i} - x_J`. -/
def loopPrecedingY {N : ℕ+} (X : LoopPrecedingConfiguration N) : Fin (N : ℕ) → ℝ :=
  fun i => cyclicLift X.val (loopPrecedingLabel X + i) - cyclicLift X.val (loopPrecedingLabel X)

/-- The gap coordinates of the preceding-particle anchor, with the zero coordinate omitted. -/
def loopPrecedingOffsets {N : ℕ+} (X : LoopPrecedingConfiguration N) : Fin ((N : ℕ) - 1) → ℝ :=
  fun i => cyclicLift X.val (loopPrecedingLabel X + (i.val + 1 : ℕ)) -
    cyclicLift X.val (loopPrecedingLabel X)

/-- The size weight `w(y) = N y_2`, with `N = n + 2` so its coordinate exists. -/
def loopSizeWeight (n : ℕ) (y : Fin (n + 1) → ℝ) : ℝ := (n + 2 : ℕ) * y 0

/-- The measure `w P*` in the size-bias part of Lemma 5.8. -/
def loopSizeBiasedLaw (P : Parameters) (n : ℕ) : Measure (Fin (n + 1) → ℝ) :=
  (anchoredLaw P (n + 1)).withDensity (fun y => ENNReal.ofReal (loopSizeWeight n y))

theorem measurableSet_loopPrecedingDomain (N : ℕ+) : MeasurableSet (loopPrecedingDomain N) := by
  simp only [loopPrecedingDomain, Set.ofPred_forall]
  exact MeasurableSet.iInter fun j =>
    (measurableSet_eq_fun (measurable_cyclicLift j)
      (show Measurable (fun _ : Configuration N => (0 : ℝ)) from measurable_const)).compl

/-- The defining carrier has full Gibbs measure. -/
theorem ae_loopPrecedingDomain (P : Parameters) (N : ℕ+) :
    ∀ᵐ X ∂gibbsMeasure P N, X ∈ loopPrecedingDomain N := by
  change ∀ᵐ X ∂gibbsMeasure P N, ∀ j : ℤ, cyclicLift X j ≠ 0
  rw [ae_all_iff]
  intro j
  have hm : (gibbsMeasure P N) {X | (cyclicLift X j : UnitAddCircle) = 0} = 0 := by
    have he := congrArg (fun μ : Measure UnitAddCircle => μ {0})
      (map_cyclicLift_gibbsMeasure P N j)
    have hz : (volume : Measure UnitAddCircle) {0} = 0 := by
      rw [← Metric.closedBall_zero, AddCircle.volume_closedBall]
      norm_num
    rw [Measure.map_apply (show Measurable (fun X : Configuration N => (cyclicLift X j : UnitAddCircle)) from
      measurable_coe_circle.comp (measurable_cyclicLift j))
      (measurableSet_singleton 0), hz] at he
    exact he
  rw [ae_iff]
  apply measure_mono_null _ hm
  intro X hX
  change (cyclicLift X j : UnitAddCircle) = 0
  simp only [Set.mem_ofPred_eq, not_not] at hX
  rw [hX]
  rfl

private theorem preceding_zero_spec {N : ℕ+} (X : LoopPrecedingConfiguration N) :
    cyclicLift X.val (loopPrecedingLabel X) < 0 ∧
      0 < cyclicLift X.val (loopPrecedingLabel X + 1) := by
  have hb : leftLift (0 : UnitAddCircle) 0 = 0 := by
    simp only [leftLift, AddCircle.coe_zero, sub_zero]
    change (AddCircle.equivIco (1 : ℝ) 0 (QuotientAddGroup.mk (0 : ℝ)) : ℝ) = 0
    rw [AddCircle.coe_equivIco_mk_apply]
    norm_num
  have h := preceding_spec X.val (show (0 : ℝ) ≤ 0 by rfl) (show (0 : ℝ) < 1 by norm_num)
  change cyclicLift X.val (sSup {j : ℤ | cyclicLift X.val j ≤ 0}) ≤ 0 ∧ _ at h
  have hJ : loopPrecedingLabel X = sSup {j : ℤ | cyclicLift X.val j ≤ 0} := by
    simp only [loopPrecedingLabel, precedingLabel, hb]
  rw [← hJ] at h
  exact ⟨lt_of_le_of_ne h.1 (X.property _), h.2⟩

/-- The preceding label brackets zero strictly on the stated carrier. -/
theorem loopPrecedingLabel_spec {N : ℕ+} (X : LoopPrecedingConfiguration N) :
    cyclicLift X.val (loopPrecedingLabel X) < 0 ∧
      0 < cyclicLift X.val (loopPrecedingLabel X + 1) := preceding_zero_spec X

theorem loopPrecedingY_zero {N : ℕ+} (X : LoopPrecedingConfiguration N) :
    loopPrecedingY X ⟨0, N.pos⟩ = 0 := by simp [loopPrecedingY]

/-- The omitted-zero vector belongs to the anchored simplex. -/
theorem loopPrecedingOffsets_mem {N : ℕ+} (X : LoopPrecedingConfiguration N) :
    loopPrecedingOffsets X ∈ anchoredDomain ((N : ℕ) - 1) := by
  have hmono := cyclicLift_strictMono X.val
  refine ⟨fun i => ⟨?_, ?_⟩, fun i j hij => ?_⟩
  · exact sub_pos.mpr (hmono (by dsimp; omega))
  · have hi : (i.val + 1 : ℤ) < (N : ℕ) := by omega
    have h := hmono (add_lt_add_left hi (loopPrecedingLabel X))
    rw [add_comm (N : ℤ), cyclicLift_add_N] at h
    dsimp [loopPrecedingOffsets]
    rw [add_comm _ (loopPrecedingLabel X)] at h
    linarith
  · dsimp [loopPrecedingOffsets]
    apply sub_lt_sub_right
    apply hmono
    have hij' : (i.val : ℤ) < j.val := by exact_mod_cast hij
    omega

/-- The displacement lies strictly between zero and the following microscopic gap. -/
theorem loopPrecedingD_mem {N : ℕ+} (X : LoopPrecedingConfiguration N) :
    0 < loopPrecedingD X ∧ loopPrecedingD X < gap X.val (loopPrecedingLabel X) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast N.pos
  have h := preceding_zero_spec X
  dsimp [loopPrecedingD, gap]
  constructor
  · exact mul_pos_of_neg_of_neg (neg_neg_of_pos hN) h.1
  · nlinarith [mul_pos hN h.2]

end Riesz1

end
