/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
public import Mathlib.Tactic
public import Riesz1.Frozen.Profile
public import Riesz1.Frozen.ZeroExtension

/-!
# Zero extension in L²: `Riesz1.zeroExtensionL2`

The zero extension retains the fixed profile's L² certificate.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- The zero extension retains the fixed profile's L² certificate. -/
theorem zeroExtensionL2 (p : Profile) :
    MemLp (fun x => (zeroExtension p x : ℂ)) 2 (volume : Measure ℝ) := by
  have h := p.property.comp_measurePreserving (AddCircle.measurePreserving_mk 1 (-(1 / 2)))
  have hsub : Set.Ioo (-(1 / 2) : ℝ) (1 / 2) ⊆ Set.Ioc (-(1 / 2)) (-(1 / 2) + 1) := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  have h' := h.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hind := (memLp_indicator_iff_restrict measurableSet_Ioo.nullMeasurableSet).mpr h'
  convert hind using 1
  funext x
  simp only [Set.indicator_apply, zeroExtension, Function.comp_apply]
  have hiff : |x| < 1 / 2 ↔ x ∈ Set.Ioo (-(1 / 2)) (1 / 2) := abs_lt
  by_cases hx : |x| < 1 / 2
  · rw [ite_eq_left hx, ite_eq_left (hiff.mp hx)]
  · rw [ite_eq_right hx, ite_eq_right (mt hiff.mpr hx), Complex.ofReal_zero]

end Riesz1

end
end
