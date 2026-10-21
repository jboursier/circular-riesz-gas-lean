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
public import Riesz1.Frozen.RieszRepresentative
public import Riesz1.Frozen.Configuration
public import Riesz1.Frozen.GibbsMeasure
public import Riesz1.Frozen.Fluctuation
public import Riesz1.Frozen.NormalLaw
public import Riesz1.Frozen.ConvergesInLaw
public import Riesz1.Frozen.PowerExponent
public import Riesz1.Frozen.PowerRieszExponent
public import Riesz1.Frozen.PowerVariance
public import Riesz1.Frozen.ParticleNumber
public import Riesz1.Frozen.ModelWellDefined
public import Riesz1.Externals.BakryEmeryProof
public import Riesz1.Externals.PrekopaLeindlerProof
public import Riesz1.Rigidity.RigidityTheorem
public import Riesz1.Bridges.CLTChainConclusions
public import Riesz1.Bridges.QuantitativeVarianceConclusion
public import Riesz1.Variance.APrioriComplete
public import Riesz1.Variance.VarAlCompactInput
public import Riesz1.Bridges.FinalChain

/-!
# Proof of `Riesz1.power_law_observable`

This module proves the statement in `Riesz1/Frozen/PowerLawObservable.lean`, assembled from the
intermediate results. They take the Bakry–Émery criterion `External.BakryEmery` and the
Prékopa–Leindler inequality `External.PrekopaLeindler` as hypotheses. Here these are supplied by
their proofs, so the theorem is unconditional. Only that statement file imports this module.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1.Main

theorem power_law_observable :
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
          (fun X => (particleNumber n : ℝ) ^ (-s / 2) * fluctuation ⟨rieszRepresentative (powerRieszExponent P a), hf⟩ X))
        (normalLaw (Real.toNNReal (powerVariance P a))) :=
  Riesz1.Internal.power_law_observable_of_input Riesz1.Externals.bakry_emery_proof Riesz1.Externals.prekopa_leindler_proof (Riesz1.Internal.aPrioriConclusion_of_externals Riesz1.Externals.bakry_emery_proof Riesz1.Externals.prekopa_leindler_proof) (Riesz1.Internal.auxiliaryVarianceReductionInput_of_externals Riesz1.Externals.bakry_emery_proof Riesz1.Externals.prekopa_leindler_proof) (Riesz1.Internal.varAlVarianceInput_of_externals Riesz1.Externals.bakry_emery_proof Riesz1.Externals.prekopa_leindler_proof)

end Riesz1.Main

end
