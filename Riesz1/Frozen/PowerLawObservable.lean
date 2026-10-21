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
import Riesz1.Main.PowerLawObservable

/-!
# Power-law observable: `Riesz1.power_law_observable`

Power-law observable CLT, its L² membership, zero mean and positive finite
limiting variance. This is Corollary 2 of the paper.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Power-law observable CLT, its L² membership, zero mean and positive finite
limiting variance. This is Corollary 2 of the paper. -/
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
  by exact Riesz1.Main.power_law_observable

end Riesz1

end
end
