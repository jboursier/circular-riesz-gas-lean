/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1Audit.CentralLimitTheorem.SolutionBasic
public import Riesz1.Frozen.CentralLimitTheorem

/-!
# Theorem 3 (CLT for singular linear statistics): the proof

The statement of the challenge, on the definitions of `SolutionBasic.lean`, proved from
`Riesz1.central_limit_theorem` of the library. The definitions of the challenge are copies of those
of the library, so the two statements agree after unfolding the definitions.
-/

@[expose] public section

namespace Riesz1Audit.CentralLimitTheorem

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace Riesz1

/-- Singular-statistic CLT and its quantitative bound, including degenerate laws.
This is Theorem 3 of the paper. -/
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
  by exact _root_.Riesz1.central_limit_theorem

end Riesz1

end

end Riesz1Audit.CentralLimitTheorem

end
