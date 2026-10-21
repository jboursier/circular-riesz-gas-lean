/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Measurability of periodic functions on the circle

A measurable periodic real-line function descends measurably to the circle,
by evaluation at its measurable representative in a fundamental interval.
-/

public section

open MeasureTheory

namespace Riesz1

lemma measurable_periodic_circle_lift {E : Type*} [MeasurableSpace E] {f : ℝ → E}
    (hf : Measurable f) (hp : Function.Periodic f 1) :
    Measurable (hp.lift : UnitAddCircle → E) := by
  have he : (hp.lift : UnitAddCircle → E) =
      f ∘ Subtype.val ∘ (AddCircle.measurableEquivIco 1 0) := by
    funext x
    change hp.lift x = f ((AddCircle.equivIco 1 0 x).val)
    rw [← hp.lift_coe, AddCircle.coe_equivIco]
  rw [he]
  exact hf.comp (measurable_subtype_coe.comp (AddCircle.measurableEquivIco 1 0).measurable)

end Riesz1
