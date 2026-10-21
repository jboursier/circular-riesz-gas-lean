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
public import Riesz1.Frozen.Fluctuation
public import Riesz1.Frozen.Profile
public import Riesz1.Frozen.CompactProfile
public import Riesz1.Frozen.Scale
public import Riesz1.Frozen.CircleSobolev
public import Riesz1.Frozen.LineSobolev
public import Riesz1.Frozen.Scales
public import Riesz1.Frozen.TestData
public import Riesz1.Frozen.Admissible
public import Riesz1.Frozen.TestAtScale
public import Riesz1.Frozen.CircleVariance
public import Riesz1.Frozen.LineVariance
public import Riesz1.Frozen.Variance
public import Riesz1.Frozen.ModelWellDefined
public import Riesz1.Frozen.RepresentsZeroExtension
public import Riesz1.Frozen.TestAtScaleL1
public import Riesz1.Externals.BakryEmeryProof
public import Riesz1.Externals.PrekopaLeindlerProof
public import Riesz1.Rigidity.RigidityTheorem
public import Riesz1.Bridges.CLTChainConclusions
public import Riesz1.Bridges.QuantitativeVarianceConclusion
public import Riesz1.Variance.APrioriComplete
public import Riesz1.Variance.VarAlCompactInput
public import Riesz1.Bridges.FinalChain

/-!
# Proof of `Riesz1.quantitative_variance`

The proof of the statement in `Riesz1/Frozen/QuantitativeVariance.lean` (Theorem 2 of the paper),
assembled from the earlier results. The Bakry–Émery criterion `External.BakryEmery` and the
Prékopa–Leindler inequality `External.PrekopaLeindler` are supplied by their proofs, so the
theorem is unconditional. Only the statement file imports this module.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1.Main

theorem quantitative_variance :
  ∀ (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1),
    let P : Parameters := ⟨(beta, s), hbeta, hs, hs1⟩
    ∀ (p : Profile) (alpha : ℝ) (d : TestData),
      (∀ ell : Scales, Admissible P p ell alpha d →
        ModelWellDefined P ∧
        ∀ N, CircleSobolev ((1 - s) / 2) (fun x => (testAtScale p (ell N) x : ℂ)) ∧
          circleVariance P p (ell N) < ⊤) ∧
      (∀ eps : ℝ, 0 < eps → ∃ C : ℝ, 0 < C ∧
        ∀ ell : Scales, Admissible P p ell alpha d → ∀ N : ℕ+,
          1 ≤ (N : ℝ) * (ell N).val →
            ∃ hF : Integrable (fluctuation ⟨testAtScale p (ell N), testAtScaleL1 p (ell N)⟩) (gibbsMeasure P N),
            variance (gibbsMeasure P N) (fluctuation ⟨testAtScale p (ell N), testAtScaleL1 p (ell N)⟩) hF < ⊤ ∧
            |(variance (gibbsMeasure P N) (fluctuation ⟨testAtScale p (ell N), testAtScaleL1 p (ell N)⟩) hF).toReal -
              ((N : ℝ) * (ell N).val) ^ s * (circleVariance P p (ell N)).toReal| ≤
                C * ((N : ℝ) * (ell N).val) ^ (max (2 * s - 1) (2 * alpha) + eps)) ∧
      ((∃ ell : Scales, Admissible P p ell alpha d) → CompactProfile p →
        ∃ f0 : Lp ℂ 2 (volume : Measure ℝ),
          RepresentsZeroExtension p f0 ∧ LineSobolev ((1 - s) / 2) f0 ∧
          lineVariance P f0 < ⊤ ∧
          ∃ C1 : ℝ, 0 < C1 ∧ ∀ a : Scale,
            CircleSobolev ((1 - s) / 2) (fun x => (testAtScale p a x : ℂ)) ∧
            circleVariance P p a < ⊤ ∧
            |(circleVariance P p a).toReal - (lineVariance P f0).toReal| ≤ C1 * a.val ^ (2 - s)) :=
  fun beta s hbeta hs hs1 => Riesz1.Internal.quantitativeVarianceConclusion_of_input Riesz1.Externals.bakry_emery_proof Riesz1.Externals.prekopa_leindler_proof (Riesz1.Internal.auxiliaryVarianceReductionInput_of_externals Riesz1.Externals.bakry_emery_proof Riesz1.Externals.prekopa_leindler_proof) (Riesz1.Internal.varAlVarianceInput_of_externals Riesz1.Externals.bakry_emery_proof Riesz1.Externals.prekopa_leindler_proof) beta s hbeta hs hs1

end Riesz1.Main

end
