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
public import Riesz1.Frozen.UnitLength
public import Riesz1.Frozen.CentralRep
public import Riesz1.Frozen.Profile
public import Riesz1.Frozen.ZeroExtension
public import Riesz1.Frozen.Scale
public import Riesz1.Frozen.RescaledProfile
public import Riesz1.Frozen.ZeroExtensionL2
public import Riesz1.Frozen.LiftL2

/-!
# Rescaled profile in L²: `Riesz1.rescaledProfileL2`

Scaling preserves L², derived from the original profile.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Scaling preserves L², derived from the original profile. -/
theorem rescaledProfileL2 (p : Profile) (ell : Scale) :
    MemLp (fun x => (rescaledProfile p ell x : ℂ)) 2 volume := by
  have hmap : MemLp (fun x => (zeroExtension p x : ℂ)) 2
      (Measure.map (fun x : ℝ => ell.val⁻¹ * x) volume) := by
    rw [Real.map_volume_mul_left (inv_ne_zero ell.property.1.ne')]
    exact (zeroExtensionL2 p).smul_measure ENNReal.ofReal_ne_top
  have hscaled := hmap.comp_of_map (measurable_const.mul measurable_id).aemeasurable
  have h := liftL2 unitLength _ hscaled
  change MemLp (fun x : UnitAddCircle =>
    (zeroExtension p (ell.val⁻¹ * centralRep unitLength x) : ℂ)) 2 volume at h
  simpa only [rescaledProfile, div_eq_mul_inv, mul_comm] using h

end Riesz1

end
end
