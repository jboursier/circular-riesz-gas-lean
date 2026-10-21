/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Frozen.Parameters
public import Riesz1.Frozen.GibbsMeasure
public import Riesz1.Frozen.Fluctuation
public import Riesz1.Frozen.Profile
public import Riesz1.Frozen.CompactProfile
public import Riesz1.Frozen.Scale
public import Riesz1.Frozen.Scales
public import Riesz1.Frozen.CircleSobolev
public import Riesz1.Frozen.LineSobolev
public import Riesz1.Frozen.TestData
public import Riesz1.Frozen.Admissible
public import Riesz1.Frozen.TestAtScale
public import Riesz1.Frozen.TestAtScaleL1
public import Riesz1.Frozen.CircleVariance
public import Riesz1.Frozen.LineVariance
public import Riesz1.Frozen.Variance
public import Riesz1.Frozen.ModelWellDefined
public import Riesz1.Frozen.RepresentsZeroExtension
public import Riesz1.Frozen.Mesoscopic
public import Riesz1.Frozen.BlDistance
public import Riesz1.Frozen.NormalLaw
public import Riesz1.Frozen.ConvergesInLaw
public import Riesz1.Frozen.ParticleNumber
public import Riesz1.Frozen.NormalizedStatistic
public import Riesz1.Frozen.StatisticLaws

/-!
# The main theorems as conclusions

The main theorems `Riesz1.quantitative_variance` (Theorem 2) and `Riesz1.central_limit_theorem`
(Theorem 3) are proved in `Riesz1/Main/`. Results that need them take their conclusions as
explicit hypotheses.

Each conclusion is a `Prop` in `Riesz1.Internal`, indexed by the same parameters as the statement
of the theorem. Its body repeats the proposition of the theorem symbol for symbol, so that the
proof of the theorem is an `exact` of the internal result.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

namespace Internal

/-- The variance conclusion of Theorem 2 for the parameters `(beta, s)`.
The body repeats the body of `Riesz1.quantitative_variance` after its binder
`∀ beta s hbeta hs hs1`, with the same `let P`. -/
def QuantitativeVarianceConclusion (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1) :
    Prop :=
  let P : Parameters := ⟨(beta, s), hbeta, hs, hs1⟩
  ∀ (p : Profile) (alpha : ℝ) (d : TestData),
    (∀ ell : Scales, Admissible P p ell alpha d →
      ModelWellDefined P ∧
      ∀ N, CircleSobolev ((1 - s) / 2) (fun x => (testAtScale p (ell N) x : ℂ)) ∧
        circleVariance P p (ell N) < ⊤) ∧
    (∀ eps : ℝ, 0 < eps → ∃ C : ℝ, 0 < C ∧
      ∀ ell : Scales, Admissible P p ell alpha d → ∀ N : ℕ+,
        1 ≤ (N : ℝ) * (ell N).val →
          ∃ hF : Integrable (fluctuation ⟨testAtScale p (ell N), testAtScaleL1 p (ell N)⟩)
              (gibbsMeasure P N),
          variance (gibbsMeasure P N) (fluctuation ⟨testAtScale p (ell N), testAtScaleL1 p (ell N)⟩)
              hF < ⊤ ∧
          |(variance (gibbsMeasure P N)
              (fluctuation ⟨testAtScale p (ell N), testAtScaleL1 p (ell N)⟩) hF).toReal -
            ((N : ℝ) * (ell N).val) ^ s * (circleVariance P p (ell N)).toReal| ≤
              C * ((N : ℝ) * (ell N).val) ^ (max (2 * s - 1) (2 * alpha) + eps)) ∧
    ((∃ ell : Scales, Admissible P p ell alpha d) → CompactProfile p →
      ∃ f0 : Lp ℂ 2 (volume : Measure ℝ),
        RepresentsZeroExtension p f0 ∧ LineSobolev ((1 - s) / 2) f0 ∧
        lineVariance P f0 < ⊤ ∧
        ∃ C1 : ℝ, 0 < C1 ∧ ∀ a : Scale,
          CircleSobolev ((1 - s) / 2) (fun x => (testAtScale p a x : ℂ)) ∧
          circleVariance P p a < ⊤ ∧
          |(circleVariance P p a).toReal - (lineVariance P f0).toReal| ≤ C1 * a.val ^ (2 - s))

/-- The CLT conclusion of Theorem 3 for the parameters `(beta, s)`. The body repeats the
body of `Riesz1.central_limit_theorem` after its binder `∀ beta s hbeta hs hs1`, with the same
`let P`. -/
def CLTConclusion (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1) : Prop :=
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
              (eps + max ((s - 1) / 2) (-r))))

end Internal

end Riesz1

end
end
