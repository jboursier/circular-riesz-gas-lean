/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1Audit.QuantitativeVariance.SolutionBasic
public import Riesz1.Frozen.QuantitativeVariance

/-!
# Theorem 2 (variance of singular linear statistics): the proof

The statement of the challenge, on the definitions of `SolutionBasic.lean`, proved from
`Riesz1.quantitative_variance` of the library. The definitions of the challenge are copies of those
of the library, so the two statements agree after unfolding the definitions.
-/

@[expose] public section

namespace Riesz1Audit.QuantitativeVariance

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Variance expansion, Sobolev and random-variable finiteness, and the compact
profile's line-variance approximation for every scale.
This is Theorem 2 of the paper. -/
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
  by exact _root_.Riesz1.quantitative_variance

end Riesz1

end

end Riesz1Audit.QuantitativeVariance

end
