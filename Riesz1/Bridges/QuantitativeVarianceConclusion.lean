/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.OptimalScalingComplete
public import Riesz1.CLT.MainConclusions

/-!
# The variance conclusion used by the corollaries

`Riesz1.Internal.QuantitativeVarianceConclusion` (the proposition of
Theorem 2 at fixed parameters) follows from
`Riesz1.Internal.quantitative_variance_of_input`.
-/

public section

namespace Riesz1.Internal

/-- `QuantitativeVarianceConclusion` at every parameter, from the inputs of
`quantitative_variance_of_input`. -/
theorem quantitativeVarianceConclusion_of_input
    (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (hAux : AuxiliaryVarianceReductionInput) (hLoop : VarAlVarianceInput)
    (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1) :
    QuantitativeVarianceConclusion beta s hbeta hs hs1 :=
  quantitative_variance_of_input hBE hPL hAux hLoop beta s hbeta hs hs1

end Riesz1.Internal

end
