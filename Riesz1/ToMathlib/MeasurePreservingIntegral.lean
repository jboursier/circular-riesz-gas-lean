/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Integrable pullbacks and their expectations

The change-of-variables formula for a measure-preserving map, with integrability supplied
on the target. Injectivity is unnecessary.
-/

public section

open MeasureTheory

namespace Riesz1

theorem integrable_integral_comp_measurePreserving
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {r : α → β}
    (hr : MeasurePreserving r μ ν) {f : β → ℝ} (hf : Integrable f ν) :
    Integrable (fun x => f (r x)) μ ∧ (∫ x, f (r x) ∂μ) = ∫ y, f y ∂ν := by
  refine ⟨hr.integrable_comp_of_integrable hf, ?_⟩
  have hm : AEStronglyMeasurable f (μ.map r) := hr.map_eq.symm ▸ hf.aestronglyMeasurable
  rw [← integral_map hr.measurable.aemeasurable hm, hr.map_eq]

end Riesz1
