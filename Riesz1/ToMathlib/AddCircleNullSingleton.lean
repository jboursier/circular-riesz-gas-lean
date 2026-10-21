/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Points of the additive circle are Haar-null

For every period `T > 0` and every point `c` of `AddCircle T`, the Haar measure `volume` gives the
singleton `{c}` measure zero. The library does not register a `NullSingletonClass` instance for
`volume` on `AddCircle T`, so the proof pulls the singleton back to an interval of `ℝ` through the
covering map, which is measure preserving on that interval.

* `addCircle_volume_singleton`: `volume {c} = 0` for every `c : AddCircle T`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

/-- Every point of the additive circle `AddCircle T`, with `T > 0`, has Haar measure zero. -/
theorem addCircle_volume_singleton (T : ℝ) [Fact (0 < T)] (c : AddCircle T) :
    volume ({c} : Set (AddCircle T)) = 0 := by
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective c
  have hmp := AddCircle.measurePreserving_mk T (t - T)
  rw [← hmp.measure_preimage (measurableSet_singleton _).nullMeasurableSet,
    Measure.restrict_apply' measurableSet_Ioc]
  refine measure_mono_null (t := {t}) ?_ (measure_singleton _)
  have ht : t ∈ Ioc (t - T) (t - T + T) := by
    have hT : 0 < T := Fact.out
    constructor <;> linarith
  rintro y ⟨hy1, hy2⟩
  have heq : (y : AddCircle T) = (t : AddCircle T) := hy1
  rw [AddCircle.coe_eq_coe_iff_of_mem_Ioc hy2 ht] at heq
  exact heq

end Riesz1

end
end
