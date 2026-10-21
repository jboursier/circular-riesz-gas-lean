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
public import Riesz1.Frozen.ParametersExponent
public import Riesz1.Frozen.GibbsMeasure
public import Riesz1.Frozen.Scales
public import Riesz1.Frozen.Mesoscopic
public import Riesz1.Frozen.NormalLaw
public import Riesz1.Frozen.ConvergesInLaw
public import Riesz1.Frozen.PeriodicZeta
public import Riesz1.Frozen.CountVariance
public import Riesz1.Frozen.ParticleNumber
public import Riesz1.Frozen.ModelWellDefined
public import Riesz1.Frozen.NormalizedCount
public import Riesz1.Frozen.NormalizedGap
import Riesz1.Main.FluctuationsGapsDiscrepancy

/-!
# Count and gap CLTs: `Riesz1.fluctuations_gaps_discrepancy`

Both count and gap CLTs. Scales need no limit. The gap range starts at N=2.
All denominators in the asserted ranges are positive conclusions.
This is Corollary 1 of the paper.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Both count and gap CLTs. Scales need no limit. The gap range starts at N=2.
All denominators in the asserted ranges are positive conclusions.
This is Corollary 1 of the paper. -/
theorem fluctuations_gaps_discrepancy :
  ∀ (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1),
    let P : Parameters := ⟨(beta, s), hbeta, hs, hs1⟩
    ModelWellDefined P ∧ 0 < countVariance P ∧
    (∀ (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2), ∀ ell : Scales, Mesoscopic ell →
      (∀ N : ℕ+, 0 < Real.sqrt ((N : ℝ) ^ s *
        periodicZeta (parametersExponent P) ((2 * a * (ell N).val : ℝ) : UnitAddCircle)) ∧
        AEMeasurable (normalizedCount P a ha ha1 ell N) (gibbsMeasure P N)) ∧
      ConvergesInLaw
        (fun n => (gibbsMeasure P (particleNumber n)).map (normalizedCount P a ha ha1 ell (particleNumber n)))
        (normalLaw (Real.toNNReal (countVariance P)))) ∧
    (∀ k : ℕ+ → ℕ,
      ∀ hk : (∀ N : ℕ+, 2 ≤ (N : ℕ) → 1 ≤ k N ∧ k N ≤ (N : ℕ) / 2),
      Tendsto (fun n => k (particleNumber n)) atTop atTop →
      (∀ (N : ℕ+) (hN : 2 ≤ (N : ℕ)),
        0 < Real.sqrt ((N : ℝ) ^ s * periodicZeta (parametersExponent P) (((k N : ℝ) / (N : ℝ) : ℝ) : UnitAddCircle)) ∧
        AEMeasurable (normalizedGap P N (k N) (hk N hN)) (gibbsMeasure P N)) ∧
      ConvergesInLaw
        (fun n => (gibbsMeasure P (particleNumber (n + 1))).map
          (normalizedGap P (particleNumber (n + 1)) (k (particleNumber (n + 1))) (hk (particleNumber (n + 1)) (Nat.le_add_left 2 n))))
        (normalLaw (Real.toNNReal (countVariance P)))) :=
  by exact Riesz1.Main.fluctuations_gaps_discrepancy

end Riesz1

end
end
