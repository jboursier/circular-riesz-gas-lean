/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Restricting a fourth moment to a rare event

Cauchy--Schwarz bounds the restricted second moment by the fourth moment
and the fourth root of the event's mass.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace Riesz1

theorem eLpNorm_two_restrict_le_four {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] {μ : Measure Ω} {f : Ω → E}
    (hf : AEStronglyMeasurable f μ) (S : Set Ω) :
    eLpNorm f 2 (μ.restrict S) ≤ eLpNorm f 4 μ * μ S ^ (1 / 4 : ℝ) := by
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (f := f) (μ := μ.restrict S)
    (show (2 : ℝ≥0∞) ≤ 4 by norm_num) hf.restrict
  norm_num only [ENNReal.toReal_ofNat, Measure.restrict_apply_univ,
    show (1 / (2 : ℝ) - 1 / 4) = 1 / 4 by norm_num] at h
  exact h.trans (mul_le_mul' (eLpNorm_restrict_le f 4 μ S) le_rfl)

end Riesz1
