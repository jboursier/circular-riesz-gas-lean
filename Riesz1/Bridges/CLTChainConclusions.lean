/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Bridges.CLTChainErrors
public import Riesz1.Bridges.QuantitativeVarianceConclusion
public import Riesz1.Variance.OptimalScalingComplete
public import Riesz1.CLT.Assembly
public import Riesz1.CLT.GapsDiscMain
public import Riesz1.CLT.PowerLawConditional
public import Riesz1.CLT.Smoothing

/-!
# The conclusions of the CLT chain, from the variance and a-priori inputs

This file discharges the conditional hypotheses of the CLT results, so that each conclusion
follows from the inputs `APrioriConclusion` (`hAP`), `VarAlVarianceInput` (`hVarAl`) and
`AuxiliaryVarianceReductionInput` (`hAux`), together with the hypotheses `hBE`
(the Bakry–Émery criterion `External.BakryEmery`) and `hPL` (the Prékopa–Leindler inequality
`External.PrekopaLeindler`):

* `assemblyVarianceConclusion_of_input` (Theorem 2): the copy
  `AssemblyVarianceConclusion` holds, since its body is that of `QuantitativeVarianceConclusion`.
* `cltConclusion_of_input` (Theorem 3): `central_limit_theorem_of_inputs`, with its two error
  copies from `CLTChainErrors.lean`, its variance copy and `quantitative_variance_uniform_of_input`.
* `fluctuations_gaps_discrepancy_of_input` (Corollary 1) and
  `power_law_observable_of_input` (Corollary 2): the `_of_variance_clt` theorems, with their
  variance and CLT hypotheses discharged.
* `clt_smoothing_complete_of_input` (smoothing part of the proof of Theorem 3): the conclusion with
  the uniform variance input discharged.

The conclusions copy the bodies of the `_of_variance_clt` statements symbol for symbol.
No step is added to a statement of the paper, and no hypothesis is weakened.
The hypothesis `hBE` is passed on because the interfaces take it, although no proof in this
chain uses it. The hypothesis `hPL` is used by the loop-error and CLT assemblies.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BoundedContinuousFunction

namespace Riesz1.Internal

/-- **Theorem 2, conditional on the inputs.** `AssemblyVarianceConclusion` holds at
every parameters `(beta, s)`, from `quantitativeVarianceConclusion_of_input`. -/
theorem assemblyVarianceConclusion_of_input (hBE : External.BakryEmery)
    (hPL : External.PrekopaLeindler) (hAux : AuxiliaryVarianceReductionInput)
    (hVarAl : VarAlVarianceInput) :
    ∀ (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1),
      AssemblyVarianceConclusion beta s hbeta hs hs1 :=
  fun beta s hbeta hs hs1 =>
    quantitativeVarianceConclusion_of_input hBE hPL hAux hVarAl beta s hbeta hs hs1

/-- **Theorem 3, conditional on the inputs.** `CLTConclusion` holds at every parameters `(beta, s)`,
from the assembly `central_limit_theorem_of_inputs` with its four inputs discharged. -/
theorem cltConclusion_of_input (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (hAP : APrioriConclusion) (hAux : AuxiliaryVarianceReductionInput)
    (hVarAl : VarAlVarianceInput) :
    ∀ (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1),
      CLTConclusion beta s hbeta hs hs1 :=
  fun beta s hbeta hs hs1 => central_limit_theorem_of_inputs hBE hPL
    (assemblyErrorOneConclusion_of_input hAP)
    (assemblyErrorTwoConclusion_of_input hAP hVarAl hPL)
    (assemblyVarianceConclusion_of_input hBE hPL hAux hVarAl)
    (quantitative_variance_uniform_of_input hBE hPL hAux hVarAl) beta s hbeta hs hs1

/-- **Corollary 1, conditional on the inputs.** The conclusion of
`fluctuations_gaps_discrepancy_of_variance_clt`, at every parameters `(beta, s)`, with its variance
and CLT hypotheses discharged. The body is that of `Riesz1.fluctuations_gaps_discrepancy`. -/
theorem fluctuations_gaps_discrepancy_of_input (hBE : External.BakryEmery)
    (hPL : External.PrekopaLeindler) (hAP : APrioriConclusion)
    (hAux : AuxiliaryVarianceReductionInput) (hVarAl : VarAlVarianceInput) :
    ∀ (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1),
    let P : Parameters := ⟨(beta, s), hbeta, hs, hs1⟩
    ModelWellDefined P ∧ 0 < countVariance P ∧
    (∀ (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2), ∀ ell : Scales, Mesoscopic ell →
      (∀ N : ℕ+, 0 < Real.sqrt ((N : ℝ) ^ s *
        periodicZeta (parametersExponent P) ((2 * a * (ell N).val : ℝ) : UnitAddCircle)) ∧
        AEMeasurable (normalizedCount P a ha ha1 ell N) (gibbsMeasure P N)) ∧
      ConvergesInLaw
        (fun n => (gibbsMeasure P (particleNumber n)).map
          (normalizedCount P a ha ha1 ell (particleNumber n)))
        (normalLaw (Real.toNNReal (countVariance P)))) ∧
    (∀ k : ℕ+ → ℕ,
      ∀ hk : (∀ N : ℕ+, 2 ≤ (N : ℕ) → 1 ≤ k N ∧ k N ≤ (N : ℕ) / 2),
      Tendsto (fun n => k (particleNumber n)) atTop atTop →
      (∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ)),
        0 < Real.sqrt ((N : ℝ) ^ s *
          periodicZeta (parametersExponent P) (((k N : ℝ) / (N : ℝ) : ℝ) : UnitAddCircle)) ∧
        AEMeasurable (normalizedGap P N (k N) (hk N hN)) (gibbsMeasure P N)) ∧
      ConvergesInLaw
        (fun n => (gibbsMeasure P (particleNumber (n + 1))).map
          (normalizedGap P (particleNumber (n + 1)) (k (particleNumber (n + 1)))
            (hk (particleNumber (n + 1)) (by change 2 ≤ n + 1 + 1; omega))))
        (normalLaw (Real.toNNReal (countVariance P)))) :=
  fun beta s hbeta hs hs1 => fluctuations_gaps_discrepancy_of_variance_clt beta s hbeta hs hs1
    hBE hPL (quantitativeVarianceConclusion_of_input hBE hPL hAux hVarAl beta s hbeta hs hs1)
    (cltConclusion_of_input hBE hPL hAP hAux hVarAl beta s hbeta hs hs1)

/-- **Corollary 2, conditional on the inputs.** The conclusion of
`power_law_observable_of_variance_clt`, at every parameters `(beta, s)`, with its CLT hypothesis
discharged. The body is that of `Riesz1.power_law_observable`. -/
theorem power_law_observable_of_input (hBE : External.BakryEmery)
    (hPL : External.PrekopaLeindler) (hAP : APrioriConclusion)
    (hAux : AuxiliaryVarianceReductionInput) (hVarAl : VarAlVarianceInput) :
    ∀ (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1),
    let P : Parameters := ⟨(beta, s), hbeta, hs, hs1⟩
    ∀ (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < s / 2),
      let a : PowerExponent P := ⟨alpha, ha, ha1⟩
      ModelWellDefined P ∧
      MemLp (fun x => (rieszRepresentative (powerRieszExponent P a) x : ℂ)) 2 volume ∧
      ∃ hf : Integrable (rieszRepresentative (powerRieszExponent P a)) volume,
      (∫ x : UnitAddCircle, rieszRepresentative (powerRieszExponent P a) x) = 0 ∧
      0 < powerVariance P a ∧
      (∀ N : ℕ+,
        AEMeasurable (fun X : Configuration N => (N : ℝ) ^ (-s / 2) *
          fluctuation ⟨rieszRepresentative (powerRieszExponent P a), hf⟩ X) (gibbsMeasure P N)) ∧
      ConvergesInLaw
        (fun n => (gibbsMeasure P (particleNumber n)).map
          (fun X => (particleNumber n : ℝ) ^ (-s / 2) *
            fluctuation ⟨rieszRepresentative (powerRieszExponent P a), hf⟩ X))
        (normalLaw (Real.toNNReal (powerVariance P a))) :=
  fun beta s hbeta hs hs1 => power_law_observable_of_variance_clt beta s hbeta hs hs1
    (cltConclusion_of_input hBE hPL hAP hAux hVarAl beta s hbeta hs hs1)

/-- **Smoothing part of the proof of Theorem 3, quantitative part, conditional on the inputs.**
The conclusion of
`clt_smoothing_complete_of_variance_uniform`, with the uniform variance input discharged. -/
theorem clt_smoothing_complete_of_input (hBE : External.BakryEmery)
    (hPL : External.PrekopaLeindler) (hAux : AuxiliaryVarianceReductionInput)
    (hVarAl : VarAlVarianceInput)
    (P : Parameters) (p : Profile) (α : ℝ) (d : TestData)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) (τ : ℝ) (hτ : 0 < τ) :
    ∃ C K₀ : ℝ, 0 < C ∧ 0 < K₀ ∧
      ∀ ell : Scales, Admissible P p ell α d →
      ∀ N : ℕ+, K₀ ≤ (N : ℝ) * (ell N).val →
        let hh := cltDelta_pos P N (ell N)
        let f := (⟨(fun x => (testAtScale p (ell N) x : ℂ)), testAtScaleL2 p (ell N)⟩ :
          {f : UnitAddCircle → ℂ // MemLp f 2 volume})
        let g := (⟨(fun x => (cltScaledLift hρ (ell N) hh
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ x : ℂ)),
          cltScaledLift_memLp hρ (ell N) hh _⟩ : {f : UnitAddCircle → ℂ // MemLp f 2 volume})
        let V := cltVariance P (ell N) (subL2 f g)
        let G := cltStat P N (ell N) (cltScaledFun hρ (ell N) hh
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩)
        V < ⊤ ∧ Real.sqrt V.toReal ≤
          C * (cltDelta P N (ell N)) ^ (P.val.2 / 2 - α - τ) ∧
          MemLp (fun X => normalizedStatistic P p ell N X - G X) 2 (gibbsMeasure P N) ∧
          (eLpNorm (fun X => normalizedStatistic P p ell N X - G X) 2 (gibbsMeasure P N)).toReal ≤
            C * ((cltDelta P N (ell N)) ^ (P.val.2 / 2 - α - τ) +
              ((N : ℝ) * (ell N).val) ^ (max ((P.val.2 - 1) / 2) (α - P.val.2 / 2) + τ)) :=
  clt_smoothing_complete_of_variance_uniform
    (quantitative_variance_uniform_of_input hBE hPL hAux hVarAl) P p α d ρ hρ τ hτ

end Riesz1.Internal

end
