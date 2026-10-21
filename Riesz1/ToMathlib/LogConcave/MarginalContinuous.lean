/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Uniqueness of continuous densities on an open interval

Equality of measures with continuous nonnegative densities on an open interval
implies pointwise equality of the densities throughout that interval.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace Riesz1

/-- The continuous nonnegative representative of an interval density is unique. -/
theorem continuous_interval_density_unique {a b : ℝ} {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Ioo a b)) (hg : ContinuousOn g (Ioo a b))
    (hfpos : ∀ x ∈ Ioo a b, 0 ≤ f x) (hgpos : ∀ x ∈ Ioo a b, 0 ≤ g x)
    (hlaw : (volume.restrict (Ioo a b)).withDensity (fun x => ENNReal.ofReal (f x)) =
      (volume.restrict (Ioo a b)).withDensity (fun x => ENNReal.ofReal (g x))) :
    EqOn f g (Ioo a b) := by
  have hfc : ContinuousOn (fun x => ENNReal.ofReal (f x)) (Ioo a b) :=
    ENNReal.continuous_ofReal.comp_continuousOn hf
  have hgc : ContinuousOn (fun x => ENNReal.ofReal (g x)) (Ioo a b) :=
    ENNReal.continuous_ofReal.comp_continuousOn hg
  have heq : (fun x => ENNReal.ofReal (f x)) =ᵐ[volume.restrict (Ioo a b)]
      (fun x => ENNReal.ofReal (g x)) :=
    (withDensity_eq_iff_of_sigmaFinite (hfc.aemeasurable measurableSet_Ioo)
      (hgc.aemeasurable measurableSet_Ioo)).mp hlaw
  have hpoint := Measure.eqOn_open_of_ae_eq heq isOpen_Ioo hfc hgc
  intro x hx
  have h := congrArg ENNReal.toReal (hpoint hx)
  simpa only [ENNReal.toReal_ofReal (hfpos x hx), ENNReal.toReal_ofReal (hgpos x hx)] using h

end Riesz1

end
end
