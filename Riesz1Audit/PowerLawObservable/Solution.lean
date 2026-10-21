/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1Audit.PowerLawObservable.SolutionBasic
public import Riesz1.Frozen.PowerLawObservable

/-!
# Corollary 2 (CLT for power-law observables): the proof

The statement of the challenge, on the definitions of `SolutionBasic.lean`, proved from
`Riesz1.power_law_observable` of the library. The definitions of the challenge are copies of those
of the library, so the two statements agree after unfolding the definitions.
-/

@[expose] public section

namespace Riesz1Audit.PowerLawObservable

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
  by exact _root_.Riesz1.power_law_observable

end Riesz1

end

end Riesz1Audit.PowerLawObservable

end
