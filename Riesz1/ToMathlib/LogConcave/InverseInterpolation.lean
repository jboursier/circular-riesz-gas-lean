/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# Interpolation of inverse moments

Probability-space Jensen for two integrable negative powers of a positive variable.
This is an input to Lemma 4.5.
-/

public section

open MeasureTheory Set

namespace Riesz1

/-- Lower inverse moments are bounded by powers of higher inverse moments. -/
theorem integral_inverse_rpow_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Y : Ω → ℝ} (hY : ∀ x, 0 < Y x)
    {p r : ℝ} (hp : 0 ≤ p) (hr : 0 < r) (hpr : p ≤ r)
    (hi : Integrable (fun x => Y x ^ (-p)) μ)
    (hj : Integrable (fun x => Y x ^ (-r)) μ) :
    (∫ x, Y x ^ (-p) ∂μ) ≤ (∫ x, Y x ^ (-r) ∂μ) ^ (p / r) := by
  have he (x : Ω) : (Y x ^ (-r)) ^ (p / r) = Y x ^ (-p) := by
    rw [← Real.rpow_mul (hY x).le]
    congr 1
    field_simp
  have hc := Real.concaveOn_rpow (div_nonneg hp hr.le) ((div_le_one hr).mpr hpr)
  have hcont : ContinuousOn (fun t : ℝ => t ^ (p / r)) (Ici 0) :=
    (Real.continuous_rpow_const (div_nonneg hp hr.le)).continuousOn
  have hh := hc.le_map_integral hcont isClosed_Ici
    (ae_of_all μ fun x => (Real.rpow_nonneg (hY x).le (-r))) hj
    (by simpa only [Function.comp_def, he] using hi)
  simpa only [he] using hh

end Riesz1
