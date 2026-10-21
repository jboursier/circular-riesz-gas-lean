/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.AuxiliaryFamilyComplete
public import Riesz1.Variance.AuxiliaryReductionFinal

/-!
# The auxiliary reduction with only the microscopic input remaining

This is part of the proof of Proposition 5.6. The derivative and energy estimates are
proved from the Bakry–Émery criterion `External.BakryEmery` and the Prékopa–Leindler
inequality `External.PrekopaLeindler`. The remaining hypothesis
is precisely the microscopic family variance estimate.
-/

public section

namespace Riesz1.Internal

/-- The complete auxiliary reduction follows from the microscopic family
estimate, `hBE` and `hPL`. Its other analytic inputs are discharged. -/
theorem auxiliaryVarianceReductionInput_of_micro
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (hMicro : AuxiliaryMicroFamilyVarianceInput) : AuxiliaryVarianceReductionInput :=
  auxiliaryVarianceReductionInput_of_input hBE hPL hMicro
    (auxiliaryDerivativeFamilyVarianceInput_of_externals hBE hPL)
    (auxiliaryTransportEnergyFamilyInput_of_externals hBE hPL)

end Riesz1.Internal
