/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.GapsDiscMainGap
public import Riesz1.CLT.GapsDiscCounts
public import Riesz1.CLT.GapsDiscStripsMain

/-!
# Interval counts and gaps, the main corollary

Corollary 1 (`Riesz1.fluctuations_gaps_discrepancy`).
The conclusion is the body of that statement, copied symbol for symbol after its binder
`∀ beta s hbeta hs hs1`, so that the proof of `Riesz1.fluctuations_gaps_discrepancy` is an `exact`
once the two main theorems, the Bakry–Émery criterion and the Prékopa–Leindler inequality are
supplied.

The count assertion is `Internal.counts_of_variance_clt`. The gap assertion is
`Internal.gap_label_zero_of_variance_clt`, whose law is the normalized gap by the identity
`normalizedGap_eq_centeredGap`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace Riesz1

/-- The normalized gap is the centred gap at the label `0`, `(S_{1,k} - k) / b_{N,k}`. -/
lemma normalizedGap_eq_centeredGap (P : Parameters) (N : ℕ+) (k : ℕ)
    (hk : 1 ≤ k ∧ k ≤ (N : ℕ) / 2) :
    normalizedGap P N k hk = fun X => centeredGap (parametersExponent P) X 0 k hk := by
  funext X
  unfold normalizedGap centeredGap gapScale blockLength
  simp only [zero_add]
  rfl

namespace Internal

/-- **Interval counts and gaps**, Corollary 1, under the two main theorems as hypotheses (in the
form of their conclusions), the Bakry–Émery criterion `hBE` and the Prékopa–Leindler inequality
`hPL`. The body is the body of `Riesz1.fluctuations_gaps_discrepancy` after its binder
`∀ beta s hbeta hs hs1`. -/
theorem fluctuations_gaps_discrepancy_of_variance_clt (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s)
    (hs1 : s < 1) (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (hQV : Internal.QuantitativeVarianceConclusion beta s hbeta hs hs1)
    (hCLT : Internal.CLTConclusion beta s hbeta hs hs1) :
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
          (normalizedGap P (particleNumber (n + 1)) (k (particleNumber (n + 1)))
            (hk (particleNumber (n + 1)) (by change 2 ≤ n + 1 + 1; omega))))
        (normalLaw (Real.toNNReal (countVariance P)))) := by
  intro P
  refine ⟨modelWellDefined P, gapsDisc_countVariance_pos P,
    counts_of_variance_clt beta s hbeta hs hs1 hQV hCLT, fun k hk hkt => ⟨fun N hN => ⟨?_, ?_⟩, ?_⟩⟩
  · exact gapsDisc_gapScale_pos (parametersExponent P) N (k N) (hk N hN).1 (hk N hN).2
  · rw [normalizedGap_eq_centeredGap]
    exact (measurable_centeredGap (parametersExponent P) 0 _ _).aemeasurable
  · simp only [normalizedGap_eq_centeredGap]
    exact gap_label_zero_of_variance_clt hBE hPL beta s hbeta hs hs1 hQV hCLT k hk hkt

end Internal

end Riesz1

end
end
