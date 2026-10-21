/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Sanity.Basic

/-!
# Sanity checks for the analytic carriers

Fourier modes and arc indicators have the certificates required by the Fourier,
Sobolev and centered-statistic definitions.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Riesz1

/-- Each mode supplies a valid integrable coefficient input, with its expected coefficient. -/
lemma coeff_fourier (k j : ℤ) :
    coeff unitLength
      ⟨fourier (T := 1) k, complexL2Integrable unitLength _ (ContinuousMap.memLp volume ℂ (fourier (T := 1) k))⟩ j =
      if k = j then 1 else 0 := by
  classical
  change fourierCoeff (fourier (T := 1) k) j = if k = j then 1 else 0
  rw [fourierCoeff_fourier]
  simp only [Pi.single_apply, eq_comm]

/-- The arc indicator is an admissible integrable input for the coefficient map. -/
lemma arcIndicator_coeff_carrier (center : UnitAddCircle) (a : ℝ) :
    Integrable (fun x => (arcIndicator center a x : ℂ)) (arclength unitLength) :=
  complexL2Integrable unitLength _ (arcIndicator_memLp center a)

/-- The real arc indicator has a finite mean, as required for fluctuation. -/
lemma arcIndicator_fluctuation_carrier (center : UnitAddCircle) (a : ℝ) :
    Integrable (arcIndicator center a) volume :=
  realL2Integrable unitLength _ (arcIndicator_memLp center a)

/-- Centering the arc test gives exactly the count minus its arclength mean. -/
lemma fluctuation_arcIndicator {N : ℕ+} (center : UnitAddCircle) (a : ℝ)
    (X : Configuration N) :
    fluctuation ⟨arcIndicator center a, arcIndicator_fluctuation_carrier center a⟩ X =
      arcCount center a X - (N : ℝ) * ∫ x, arcIndicator center a x := by
  rfl

/-- The integrable constant random variable has variance zero under a probability law. -/
lemma variance_const {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω)
    [IsProbabilityMeasure mu] (c : ℝ) :
    variance mu (fun _ => c) (integrable_const c) = 0 := by
  simp [variance]

/-- Scale one retains the fixed profile's actual representative. -/
lemma testAtScale_one (p : Profile) :
    testAtScale p ⟨1, zero_lt_one, le_rfl⟩ = p.val := by
  simp [testAtScale]

/-- The zero profile stays zero at every scale. Its L² certificate is constructed. -/
lemma testAtScale_zero (ell : Scale) :
    testAtScale ⟨fun _ => 0, by simp⟩ ell =
      (fun _ => 0) := by
  funext x
  unfold testAtScale
  split_ifs <;> simp [rescaledProfile, zeroExtension]

end Riesz1

end
end
