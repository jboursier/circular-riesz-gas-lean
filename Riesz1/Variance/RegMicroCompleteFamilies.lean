/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroComplete
public import Riesz1.Variance.RegMicroFamilyCompleteInput

/-!
# The full microscopic variance input for the two families

Lemma 5.3, uniform over the two convolution families, with the constant
chosen before the scale sequence. The Fourier comparison transfers the original-profile
bound to the original test and both actual `OptimalScalingTest` families,
with one coefficient before their additional smoothing radius.
-/

public section

namespace Riesz1.Internal

/-- Microscopic regularization variance for the original test and both
families, with no separation hypothesis and only the Bakry–Émery criterion and
the Prékopa–Leindler inequality as hypotheses. -/
theorem regMicroFamily_of_externals
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler) :
    AuxiliaryMicroFamilyVarianceInput :=
  auxiliaryMicroFamilyVarianceInput_of_original (auxiliaryMicroVarianceInput_of_externals hBE hPL)

/-- The remaining microscopic input of Proposition 5.6, in the exact
encoding consumed by `auxiliaryVarianceReductionInput_of_micro`. -/
theorem auxiliaryMicroFamilyVarianceInput_of_externals
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler) :
    AuxiliaryMicroFamilyVarianceInput :=
  regMicroFamily_of_externals hBE hPL

end Riesz1.Internal
