/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Bridges.CLTChainConclusions
public import Riesz1.Variance.APrioriComplete
public import Riesz1.Variance.VarAlCompactInput
public import Riesz1.Variance.AuxiliaryCompleteReduction
public import Riesz1.Variance.RegMicroCompleteFamilies

/-!
# The variance and CLT chain from the Bakry–Émery and Prékopa–Leindler hypotheses

The variance and CLT results of the paper take two external inputs as hypotheses, the Bakry–Émery
criterion `External.BakryEmery` and the Prékopa–Leindler inequality `External.PrekopaLeindler`.
These inputs are proved in `Riesz1/Externals/`, so the main theorems are unconditional.
The three inputs of the conditional chain are proved:
`Riesz1.Internal.aPrioriConclusion_of_externals` (Lemma 5.2),
`Riesz1.Internal.varAlVarianceInput_of_externals` (Proposition 5.9) and, through
`Riesz1.Internal.auxiliaryMicroFamilyVarianceInput_of_externals` (Lemma 5.3), the input
`Riesz1.Internal.AuxiliaryVarianceReductionInput` (Proposition 5.6). The statements of the
main results follow from the bridges of `Riesz1/Bridges/CLTChainConclusions.lean`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BoundedContinuousFunction

namespace Riesz1.Internal

/-- Proposition 5.6, uniformly over the original test and both families, from the Bakry–Émery
criterion and the Prékopa–Leindler inequality only. -/
theorem auxiliaryVarianceReductionInput_of_externals (hBE : External.BakryEmery)
    (hPL : External.PrekopaLeindler) : AuxiliaryVarianceReductionInput :=
  auxiliaryVarianceReductionInput_of_micro hBE hPL
    (auxiliaryMicroFamilyVarianceInput_of_externals hBE hPL)

end Riesz1.Internal

namespace Riesz1

/-- **Proposition 5.6**, for every profile, uniformly over the original test (the branch
`v = testAtScale p ℓ_N`, `f = ξ` of `Riesz1.Internal.OptimalScalingTest`) and the two families. -/
theorem auxiliary_variance_reduction (hBE : External.BakryEmery)
    (hPL : External.PrekopaLeindler) : Internal.AuxiliaryVarianceReductionInput :=
  Internal.auxiliaryVarianceReductionInput_of_externals hBE hPL

/-- **Theorem 2**: the conclusion of `Riesz1.quantitative_variance` at every parameters. -/
theorem quantitative_variance_of_externals (hBE : External.BakryEmery)
    (hPL : External.PrekopaLeindler) :
    ∀ (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1),
      Internal.QuantitativeVarianceConclusion beta s hbeta hs hs1 :=
  fun beta s hbeta hs hs1 => Internal.quantitativeVarianceConclusion_of_input hBE hPL
    (Internal.auxiliaryVarianceReductionInput_of_externals hBE hPL)
    (Internal.varAlVarianceInput_of_externals hBE hPL) beta s hbeta hs hs1

/-- **Uniform version of Theorem 2.** -/
theorem quantitative_variance_uniform (hBE : External.BakryEmery)
    (hPL : External.PrekopaLeindler) : Internal.QuantitativeVarianceUniformConclusion :=
  Internal.quantitative_variance_uniform_of_input hBE hPL
    (Internal.auxiliaryVarianceReductionInput_of_externals hBE hPL)
    (Internal.varAlVarianceInput_of_externals hBE hPL)

/-- **Theorem 3**: the conclusion of `Riesz1.central_limit_theorem` at every parameters. -/
theorem central_limit_theorem_of_externals (hBE : External.BakryEmery)
    (hPL : External.PrekopaLeindler) :
    ∀ (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1),
      Internal.CLTConclusion beta s hbeta hs hs1 :=
  Internal.cltConclusion_of_input hBE hPL (Internal.aPrioriConclusion_of_externals hBE hPL)
    (Internal.auxiliaryVarianceReductionInput_of_externals hBE hPL)
    (Internal.varAlVarianceInput_of_externals hBE hPL)

/-- **Smoothing part of the proof of Theorem 3**, both quantitative assertions with one constant and
threshold (the Lipschitz assertion is `Riesz1.clt_smoothing_lipschitz`). -/
theorem clt_smoothing_complete (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
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
  Internal.clt_smoothing_complete_of_input hBE hPL
    (Internal.auxiliaryVarianceReductionInput_of_externals hBE hPL)
    (Internal.varAlVarianceInput_of_externals hBE hPL) P p α d ρ hρ τ hτ

end Riesz1

end
