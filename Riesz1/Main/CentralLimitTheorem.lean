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
public import Riesz1.Frozen.Parameters
public import Riesz1.Frozen.GibbsMeasure
public import Riesz1.Frozen.Profile
public import Riesz1.Frozen.CompactProfile
public import Riesz1.Frozen.CircleSobolev
public import Riesz1.Frozen.LineSobolev
public import Riesz1.Frozen.Scales
public import Riesz1.Frozen.Mesoscopic
public import Riesz1.Frozen.TestData
public import Riesz1.Frozen.Admissible
public import Riesz1.Frozen.TestAtScale
public import Riesz1.Frozen.CircleVariance
public import Riesz1.Frozen.LineVariance
public import Riesz1.Frozen.BlDistance
public import Riesz1.Frozen.NormalLaw
public import Riesz1.Frozen.ConvergesInLaw
public import Riesz1.Frozen.ParticleNumber
public import Riesz1.Frozen.ModelWellDefined
public import Riesz1.Frozen.NormalizedStatistic
public import Riesz1.Frozen.StatisticLaws
public import Riesz1.Frozen.RepresentsZeroExtension
public import Riesz1.Externals.BakryEmeryProof
public import Riesz1.Externals.PrekopaLeindlerProof
public import Riesz1.Rigidity.RigidityTheorem
public import Riesz1.Bridges.CLTChainConclusions
public import Riesz1.Bridges.QuantitativeVarianceConclusion
public import Riesz1.Variance.APrioriComplete
public import Riesz1.Variance.VarAlCompactInput
public import Riesz1.Bridges.FinalChain

/-!
# Proof of `Riesz1.central_limit_theorem`

This module proves the statement in `Riesz1/Frozen/CentralLimitTheorem.lean`, assembled from the
results with the external inputs discharged by their proofs. Only that statement file imports
this module.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1.Main

theorem central_limit_theorem :
  ∀ (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1),
    let P : Parameters := ⟨(beta, s), hbeta, hs, hs1⟩
    ∀ (p : Profile) (alpha : ℝ) (d : TestData),
      (∀ ell : Scales, Admissible P p ell alpha d → Mesoscopic ell →
        ModelWellDefined P ∧
        (∀ N, CircleSobolev ((1 - s) / 2) (fun x => (testAtScale p (ell N) x : ℂ)) ∧
          circleVariance P p (ell N) < ⊤ ∧
          AEMeasurable (normalizedStatistic P p ell N) (gibbsMeasure P N)) ∧
        (((∀ N, (ell N).val = 1) →
          ConvergesInLaw (statisticLaws P p ell)
            (normalLaw (circleVariance P p ⟨1, zero_lt_one, le_rfl⟩).toNNReal)) ∧
         ((CompactProfile p ∧
            Tendsto (fun n => (ell (particleNumber n)).val) atTop (𝓝 0)) →
          ∃ f0 : Lp ℂ 2 (volume : Measure ℝ),
            RepresentsZeroExtension p f0 ∧ LineSobolev ((1 - s) / 2) f0 ∧
            lineVariance P f0 < ⊤ ∧
            ConvergesInLaw (statisticLaws P p ell) (normalLaw (lineVariance P f0).toNNReal)))) ∧
      (let r := (2 - s) * (s - 2 * alpha) / (2 * (4 + s))
       ∀ eps : ℝ, 0 < eps → ∃ C : ℝ, 0 < C ∧
        ∀ ell : Scales, Admissible P p ell alpha d → Mesoscopic ell →
          0 < r ∧ ∀ N : ℕ+, 1 ≤ (N : ℝ) * (ell N).val →
            ∃ law : ProbabilityMeasure ℝ,
              (law : Measure ℝ) = (gibbsMeasure P N).map (normalizedStatistic P p ell N) ∧
              blDistance law
                ⟨normalLaw (circleVariance P p (ell N)).toNNReal,
                  by unfold normalLaw; infer_instance⟩ ≤
              ENNReal.ofReal (C * ((N : ℝ) * (ell N).val) ^
                (eps + max ((s - 1) / 2) (-r)))) :=
  Riesz1.Internal.cltConclusion_of_input Riesz1.Externals.bakry_emery_proof Riesz1.Externals.prekopa_leindler_proof (Riesz1.Internal.aPrioriConclusion_of_externals Riesz1.Externals.bakry_emery_proof Riesz1.Externals.prekopa_leindler_proof) (Riesz1.Internal.auxiliaryVarianceReductionInput_of_externals Riesz1.Externals.bakry_emery_proof Riesz1.Externals.prekopa_leindler_proof) (Riesz1.Internal.varAlVarianceInput_of_externals Riesz1.Externals.bakry_emery_proof Riesz1.Externals.prekopa_leindler_proof)

end Riesz1.Main

end
