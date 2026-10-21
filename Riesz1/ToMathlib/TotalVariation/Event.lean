/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.Hahn
public import Mathlib.MeasureTheory.Measure.TotalVariation.Basic
public import Mathlib.MeasureTheory.VectorMeasure.Operations
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic

/-!
# Total variation between probability measures: events and suprema

Let `μ ν` be probability measures on a measurable space `Ω`. Mathlib's `etvDist μ ν` is the full
variation norm, which is twice the event distance `sup_A |μ A - ν A|`.
This file proves three facts about `etvDist μ ν`.

* Every event `A` satisfies `|μ A - ν A| ≤ (etvDist μ ν).toReal / 2`, and `etvDist μ ν ≤ 2`.
* The number `(etvDist μ ν).toReal / 2` is the least upper bound of the event discrepancies, and a
  Hahn set attains it.

The auxiliary lemma `enorm_measureReal_sub_add_enorm_compl_le_etvDist` is the two-set form of the
bound: the discrepancies of a set and its complement add up to at most `etvDist μ ν`.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace Riesz1

variable {Ω : Type*} [MeasurableSpace Ω]

/-- For finite measures `μ ν` and a measurable set `S`, the discrepancies `μ S - ν S` and
`μ Sᶜ - ν Sᶜ` satisfy `‖μ S - ν S‖ₑ + ‖μ Sᶜ - ν Sᶜ‖ₑ ≤ etvDist μ ν`. The two sets form a
partition, and the variation of `μ - ν` on the whole space splits over that partition. -/
lemma enorm_measureReal_sub_add_enorm_compl_le_etvDist (μ ν : Measure Ω) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {S : Set Ω} (hS : MeasurableSet S) :
    ‖μ.real S - ν.real S‖ₑ + ‖μ.real Sᶜ - ν.real Sᶜ‖ₑ ≤ etvDist μ ν := by
  rw [etvDist_eq_etvDist_toSignedMeasure, VectorMeasure.etvDist]
  calc ‖μ.real S - ν.real S‖ₑ + ‖μ.real Sᶜ - ν.real Sᶜ‖ₑ
      = ‖(μ.toSignedMeasure - ν.toSignedMeasure) S‖ₑ
          + ‖(μ.toSignedMeasure - ν.toSignedMeasure) Sᶜ‖ₑ := by
        rw [Measure.toSignedMeasure_sub_apply hS, Measure.toSignedMeasure_sub_apply hS.compl]
    _ ≤ (μ.toSignedMeasure - ν.toSignedMeasure).variation S
          + (μ.toSignedMeasure - ν.toSignedMeasure).variation Sᶜ :=
        add_le_add (VectorMeasure.enorm_measure_le_variation _ _)
          (VectorMeasure.enorm_measure_le_variation _ _)
    _ = (μ.toSignedMeasure - ν.toSignedMeasure).variation Set.univ :=
        measure_add_measure_compl hS

/-- Event bound: for probability measures `μ ν` and a measurable event `A`, the discrepancy
`|μ A - ν A|` is at most `(etvDist μ ν).toReal / 2`. The complementary discrepancy equals the
negative of the first one, so the two-set bound doubles it. -/
theorem abs_measureReal_sub_le_etvDist_div_two (μ ν : Measure Ω) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {A : Set Ω} (hA : MeasurableSet A) :
    |μ.real A - ν.real A| ≤ (etvDist μ ν).toReal / 2 := by
  have h := enorm_measureReal_sub_add_enorm_compl_le_etvDist μ ν hA
  rw [probReal_compl_eq_one_sub (μ := μ) hA, probReal_compl_eq_one_sub (μ := ν) hA] at h
  have hneg : 1 - μ.real A - (1 - ν.real A) = -(μ.real A - ν.real A) := by ring
  rw [hneg, enorm_neg, Real.enorm_eq_ofReal_abs,
    ← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)] at h
  have h3 := (ENNReal.ofReal_le_iff_le_toReal (etvDist_ne_top μ ν)).1 h
  linarith

/-- The event distance of two probability measures is at most `2`. -/
theorem etvDist_le_two (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    etvDist μ ν ≤ 2 := by
  calc etvDist μ ν ≤ μ Set.univ + ν Set.univ := etvDist_le_add
    _ = 2 := by rw [measure_univ, measure_univ, one_add_one_eq_two]

/-- Supremum: for probability measures `μ ν`, the number `(etvDist μ ν).toReal / 2` is the least
upper bound of `|μ A - ν A|` over measurable `A`. The upper bound is
`abs_measureReal_sub_le_etvDist_div_two`. The bound is attained on a Hahn set `s` for `μ, ν`:
there `μ s ≤ ν s` and `ν sᶜ ≤ μ sᶜ`, so the total variation equals `2 (ν s - μ s)`. -/
theorem isLUB_abs_measureReal_sub_etvDist (μ ν : Measure Ω) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    IsLUB ((fun A : Set Ω => |μ.real A - ν.real A|) '' {A | MeasurableSet A})
      ((etvDist μ ν).toReal / 2) := by
  obtain ⟨s, hs⟩ := exists_isHahnDecomposition μ ν
  refine IsGreatest.isLUB ⟨⟨s, hs.measurableSet, ?_⟩, ?_⟩
  · dsimp only
    have htv : (etvDist μ ν).toReal = ν.real s - μ.real s + (μ.real sᶜ - ν.real sᶜ) :=
      hs.tvDist_eq
    rw [probReal_compl_eq_one_sub (μ := μ) hs.measurableSet,
      probReal_compl_eq_one_sub (μ := ν) hs.measurableSet] at htv
    have hdiff : ν.real s - μ.real s = (etvDist μ ν).toReal / 2 := by linarith
    have hsign : 0 ≤ ν.real s - μ.real s := by
      rw [hdiff]
      exact div_nonneg ENNReal.toReal_nonneg zero_le_two
    rw [abs_sub_comm, abs_of_nonneg hsign]
    exact hdiff
  · rintro _ ⟨A, hA, rfl⟩
    exact abs_measureReal_sub_le_etvDist_div_two μ ν hA

end Riesz1
