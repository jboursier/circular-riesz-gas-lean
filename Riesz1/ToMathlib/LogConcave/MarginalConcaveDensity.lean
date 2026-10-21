/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# The density of a coordinate marginal

Tonelli's theorem identifies a marginal of a product density with its fiber
integral, before any real integrals or finiteness assertions are used.
-/

@[expose] public section

open MeasureTheory Set

namespace Riesz1

/-- The first marginal of a product density is its nonnegative fiber integral. -/
theorem map_fst_withDensity_fiber {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (F : α × β → ENNReal) (hF : Measurable F) :
    ((μ.prod ν).withDensity F).map Prod.fst =
      μ.withDensity (fun x => ∫⁻ y, F (x, y) ∂ν) := by
  ext A hA
  rw [Measure.map_apply measurable_fst hA, withDensity_apply _ (measurable_fst hA),
    withDensity_apply _ hA]
  have hpre : Prod.fst ⁻¹' A = A ×ˢ (Set.univ : Set β) := by ext p; simp
  rw [hpre, ← Measure.restrict_prod_eq_prod_univ]
  exact lintegral_prod F hF.aemeasurable

end Riesz1

end
