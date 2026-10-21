/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.AssemblyInput
public import Riesz1.CLT.ErrorOneMain
public import Riesz1.CLT.ErrorTwoFinal
public import Riesz1.Bridges.InputConsolidation

/-!
# The two error conclusions of the CLT chain, from the variance and a-priori inputs

The two copies of the error bounds of the paper, `AssemblyErrorOneConclusion` (the first error bound
in the proof of Theorem 3) and `AssemblyErrorTwoConclusion` (the second error bound in the proof of
Theorem 3), follow from the conditional results:

* `assemblyErrorOneConclusion_of_input`: from `APrioriConclusion`, through `clt_error1_of_apriori`.
  The copy takes the last conjunct of `ErrorOneConclusion`, whose integrand is `errorOneStein`, the
  integral of the copy. The threshold `τ₀ = 1` is valid for every `τ > 0`.
* `assemblyErrorTwoConclusion_of_input`: from `APrioriConclusion`, `VarAlVarianceInput` and the
  Prékopa–Leindler inequality `External.PrekopaLeindler`, through `clt_error2_of_input`. The copy
  quantifies `u` as a `C¹` function with a bound `B` (not as a continuous function with `0 ≤ M`).
  Continuity follows from `ContDiff`, and `0 ≤ B` follows from the bound at the origin.
-/

@[expose] public section

open MeasureTheory
open scoped ContDiff

namespace Riesz1.Internal

/-- **First error bound in the proof of Theorem 3, conditional on the inputs.** The copy
`AssemblyErrorOneConclusion` holds under the a-priori conclusion `APrioriConclusion` (Lemma 5.2).
Its constant is chosen after `τ`,
before the scale sequence and the particle number, as in `clt_error1_of_apriori`. -/
theorem assemblyErrorOneConclusion_of_input (hAP : APrioriConclusion) :
    AssemblyErrorOneConclusion := by
  intro P p α d ρ hρ
  refine ⟨1, one_pos, fun τ hτ _ => ?_⟩
  obtain ⟨C, K₀, hC, hK₀, hcon⟩ := clt_error1_of_apriori hAP P p α d hρ τ hτ
  refine ⟨C, K₀, hC, hK₀, fun ell hadm N hN ψ hψ htr σ hσV u hu _hB M hM => ?_⟩
  exact (hcon ell hadm N hN ψ hψ htr σ hσV).2.2.2 u hu _hB M hM

/-- **Second error bound in the proof of Theorem 3, conditional on the inputs.** The copy
`AssemblyErrorTwoConclusion` holds under the a-priori conclusion `APrioriConclusion`, the
loop-variance input `VarAlVarianceInput` (Proposition 5.9) and the Prékopa–Leindler inequality
`External.PrekopaLeindler`. Its constant is chosen after `τ`, before
the scale sequence and the particle number, as in `clt_error2_of_input`. -/
theorem assemblyErrorTwoConclusion_of_input (hAP : APrioriConclusion)
    (hVarAl : VarAlVarianceInput) (hPL : External.PrekopaLeindler) :
    AssemblyErrorTwoConclusion := by
  intro P p α d ρ hρ
  refine ⟨1, one_pos, fun τ hτ _ => ?_⟩
  obtain ⟨C, K₀, hC, hK₀, hcon⟩ := clt_error2_of_input hAP
    (errorTwoLoopVarianceInput_of_varAlVarianceInput hVarAl) hPL P p α d hρ τ hτ
  refine ⟨C, K₀, hC, hK₀, fun ell hadm N hN ψ hψ htr u hu B hB => ?_⟩
  obtain ⟨_, _, _, hcov⟩ := hcon ell hadm N hN ψ hψ htr
  exact hcov u hu.continuous B ((abs_nonneg (u 0)).trans (hB 0)) hB

end Riesz1.Internal

end
