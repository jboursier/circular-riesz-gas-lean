/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroLargeFamilies
public import Riesz1.Variance.AuxiliaryReductionFinalInput

/-!
# Extending the microscopic variance input to both families

This internal implication transfers Lemma 5.3 for
the original fixed profile to both convolution families. The common
coefficient is chosen before the scale sequence and family radius.
-/

public section

open MeasureTheory

namespace Riesz1.Internal

/-- The original-profile input implies the entire family input, by
Gibbs Fourier contraction, with exactly four times its coefficient. -/
theorem auxiliaryMicroFamilyVarianceInput_of_original
    (h : AuxiliaryMicroVarianceInput) : AuxiliaryMicroFamilyVarianceInput := by
  intro P p α d ρ hρ r _hr _hrhalf ε hε
  obtain ⟨C, hC, hb⟩ := h P p α d ρ hρ ε hε
  refine ⟨4*C, by positivity, fun ell hadm N hK v f hv => ?_⟩
  obtain ⟨hξ, hξb⟩ := hb ell hadm N hK
  obtain ⟨hE, he⟩ := regMicroFamily_bound_of_original P p ell N hρ r v f hv _
    (hξ.integrable one_le_two) hξb
  refine ⟨hE, ?_⟩
  simpa only [mul_assoc] using he

end Riesz1.Internal
