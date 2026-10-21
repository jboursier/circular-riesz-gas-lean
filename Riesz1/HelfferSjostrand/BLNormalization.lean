/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.Tilted
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Normalization on bounded open Euclidean domains

A potential continuous on the closure has a finite, strictly positive
normalizing integral on a nonempty bounded open domain. Every function
continuous on the closure is integrable under the normalized density.

These facts require neither convexity nor the Prékopa–Leindler hypothesis.
They are ingredients of the proof of Lemma 3.6.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Riesz1

variable {d : ℕ} {U : Set (EuclideanSpace ℝ (Fin d))}
variable {V F : EuclideanSpace ℝ (Fin d) → ℝ}

/-- Integrability on a bounded domain of a function continuous on its closure. -/
theorem bl_integrableOn_of_continuousOn_closure (hU : Bornology.IsBounded U)
    (ho : IsOpen U) (hF : ContinuousOn F (closure U)) : IntegrableOn F U volume :=
  hF.integrableOn_of_subset_isCompact hU.isCompact_closure ho.measurableSet
    subset_closure (hU.measure_lt_top.ne)

/-- Finiteness of the unnormalized density. -/
theorem bl_exp_neg_integrableOn (hU : Bornology.IsBounded U)
    (ho : IsOpen U) (hV : ContinuousOn V (closure U)) :
    IntegrableOn (fun x => Real.exp (-V x)) U volume :=
  bl_integrableOn_of_continuousOn_closure hU ho
    (Real.continuous_exp.comp_continuousOn hV.neg)

/-- Positivity of the normalizing integral. Integrability is established first. -/
theorem bl_normalization_pos (hU : Bornology.IsBounded U) (ho : IsOpen U)
    (hne : U.Nonempty) (hV : ContinuousOn V (closure U)) :
    0 < ∫ x in U, Real.exp (-V x) := by
  have : NeZero (volume.restrict U) :=
    ⟨fun hz => (ho.measure_pos volume hne).ne' (Measure.restrict_eq_zero.mp hz)⟩
  exact integral_exp_pos (bl_exp_neg_integrableOn hU ho hV)

/-- The nonnegative normalizing integral is positive and finite as an extended real. -/
theorem bl_normalization_lintegral_bounds (hU : Bornology.IsBounded U) (ho : IsOpen U)
    (hne : U.Nonempty) (hV : ContinuousOn V (closure U)) :
    0 < ∫⁻ x in U, ENNReal.ofReal (Real.exp (-V x)) ∧
      (∫⁻ x in U, ENNReal.ofReal (Real.exp (-V x))) < ∞ := by
  have hi := bl_exp_neg_integrableOn hU ho hV
  have heq := ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun x => (Real.exp_pos (-V x)).le))
  rw [← heq]
  exact ⟨ENNReal.ofReal_pos.mpr (bl_normalization_pos hU ho hne hV), ENNReal.ofReal_lt_top⟩

/-- The normalized Gibbs density on the domain is a probability measure. -/
theorem bl_isProbabilityMeasure (hU : Bornology.IsBounded U) (ho : IsOpen U)
    (hne : U.Nonempty) (hV : ContinuousOn V (closure U)) :
    IsProbabilityMeasure ((volume.restrict U).tilted (fun x => -V x)) := by
  have : NeZero (volume.restrict U) :=
    ⟨fun hz => (ho.measure_pos volume hne).ne' (Measure.restrict_eq_zero.mp hz)⟩
  exact isProbabilityMeasure_tilted (bl_exp_neg_integrableOn hU ho hV)

/-- Continuous observables on the compact closure are integrable for the Gibbs law. -/
theorem bl_integrable_tilted_of_continuousOn_closure (hU : Bornology.IsBounded U)
    (ho : IsOpen U) (hV : ContinuousOn V (closure U))
    (hF : ContinuousOn F (closure U)) :
    Integrable F ((volume.restrict U).tilted (fun x => -V x)) := by
  apply (integrable_tilted_iff (bl_exp_neg_integrableOn hU ho hV) F).2
  exact bl_integrableOn_of_continuousOn_closure hU ho
    ((Real.continuous_exp.comp_continuousOn hV.neg).smul hF)

/-- In particular, the centered square defining the variance is integrable. -/
theorem bl_centered_sq_integrable (hU : Bornology.IsBounded U) (ho : IsOpen U)
    (hV : ContinuousOn V (closure U)) (hF : ContinuousOn F (closure U)) :
    Integrable
      (fun x => (F x - ∫ y, F y ∂((volume.restrict U).tilted (fun y => -V y))) ^ 2)
      ((volume.restrict U).tilted (fun x => -V x)) :=
  bl_integrable_tilted_of_continuousOn_closure hU ho hV
    ((hF.sub continuousOn_const).pow 2)

/-- The extended real variance integral is finite, before any conversion to a real integral. -/
theorem bl_centered_sq_lintegral_lt_top (hU : Bornology.IsBounded U) (ho : IsOpen U)
    (hV : ContinuousOn V (closure U)) (hF : ContinuousOn F (closure U)) :
    (∫⁻ x, ENNReal.ofReal
      ((F x - ∫ y, F y ∂((volume.restrict U).tilted (fun y => -V y))) ^ 2)
      ∂((volume.restrict U).tilted (fun x => -V x))) < ∞ := by
  rw [← ofReal_integral_eq_lintegral_ofReal (bl_centered_sq_integrable hU ho hV hF)
    (Filter.Eventually.of_forall (fun x => sq_nonneg _))]
  exact ENNReal.ofReal_lt_top

end Riesz1

end
