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
public import Riesz1.Frozen.CyclicLift
public import Riesz1.Frozen.GibbsMeasure
public import Riesz1.Frozen.ArcCount
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
# Proof of `Riesz1.almost_optimal_rigidity`

The proof of the statement in `Riesz1/Frozen/AlmostOptimalRigidity.lean` (Theorem 1 of the paper),
assembled from the earlier results. The Bakry–Émery criterion `External.BakryEmery` and the
Prékopa–Leindler inequality `External.PrekopaLeindler` are supplied by their proofs, so the
theorem is unconditional. Only the statement file imports this module.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1.Main

theorem almost_optimal_rigidity :
  ∀ (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1),
    let P : Parameters := ⟨(beta, s), hbeta, hs, hs1⟩
    ModelWellDefined P ∧
    ∃ eps0 : ℝ, 0 < eps0 ∧ ∀ eps : ℝ, 0 < eps → eps < eps0 →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
        ∀ N : ℕ+,
          (∀ (i : Fin (N : ℕ)) (k : ℕ), 1 ≤ k → k ≤ (N : ℕ) / 2 →
            gibbsMeasure P N {X |
              |(N : ℝ) * (cyclicLift X ((i.val : ℤ) + k) - cyclicLift X i.val) - k| ≥
                (k : ℝ) ^ (s / 2 + eps)} ≤
              ENNReal.ofReal (C * Real.exp (-c * (k : ℝ) ^ (eps / (4 * (s + 2)))))) ∧
          (∀ (x : UnitAddCircle) (ell : ℝ), 0 < ell → ell ≤ 1 / 4 →
            gibbsMeasure P N {X |
              |arcCount x ell X - 2 * (N : ℝ) * ell| ≥
                ((N : ℝ) * ell) ^ (s / 2 + eps)} ≤
              ENNReal.ofReal (C * Real.exp (-c * ((N : ℝ) * ell) ^ (eps / (4 * (s + 2)))))) :=
  Riesz1.almost_optimal_rigidity_of_externals Riesz1.Externals.bakry_emery_proof Riesz1.Externals.prekopa_leindler_proof

end Riesz1.Main

end
