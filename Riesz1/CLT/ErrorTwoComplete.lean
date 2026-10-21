/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.ErrorTwoFinal
public import Riesz1.Variance.APrioriComplete
public import Riesz1.Variance.VarAlCompactInput

/-!
# The second Stein error

The second error bound in the proof of Theorem 3, every assertion, with only the Bakry–Émery
criterion `External.BakryEmery` and the Prékopa–Leindler inequality `External.PrekopaLeindler` as
hypotheses: the conditional `Riesz1.Internal.clt_error2_of_input` with its a priori input
discharged by `Riesz1.Internal.aPrioriConclusion_of_externals` and its loop-variance input by
`Riesz1.Internal.varAlVarianceInput_of_externals`.
-/

public section

open MeasureTheory
open scoped ContDiff ENNReal

namespace Riesz1

/-- **Second error bound in the proof of Theorem 3.** For every positive loss `τ` there are
`C, K₀ > 0`, chosen before the scale sequence, such that for every admissible scale sequence,
every `N` with `Nℓ_N ≥ K₀` and every transport `ψ` of the regularized profile, the loop statistic
and the derivative fluctuation are integrable with variances summing to at most
`C K^{2τ} (K + K^{2(1-s+α)})`, and every continuous test `u` bounded by `M ≥ 0` has
`|Error²_N(u)| ≤ C M K^{max((s-1)/2, α-s/2)+τ}`. -/
theorem clt_error2 (hBE : External.BakryEmery) (hPL : External.PrekopaLeindler)
    (P : Parameters) (p : Profile) (α : ℝ)
    (d : TestData) {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (τ : ℝ) (hτ : 0 < τ) :
    ∃ C K₀ : ℝ, 0 < C ∧ 0 < K₀ ∧
      ∀ ell : Scales, Admissible P p ell α d →
        ∀ N : ℕ+, K₀ ≤ (N : ℝ) * (ell N).val →
          ∀ ψ : Circle (loopMasterLength (ell N)) → ℝ,
            ∀ hψ : ContDiff ℝ ∞ (fun x : ℝ => ψ (x : Circle (loopMasterLength (ell N)))),
              (∀ k : ℤ, coeff (loopMasterLength (ell N))
                ⟨(fun z => (ψ z : ℂ)), complexL2Integrable _ _
                  (loopMasterLengthTest _ ψ hψ).property⟩ k =
                transportCoeffs P (loopMasterLength (ell N))
                  (loopMasterLengthTest _ (cltReg hρ P N (ell N)
                    ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩)
                    (cltReg_contDiff hρ P N (ell N) _)) k) →
              ∃ hL : Integrable (loopOnConfiguration (parametersExponent P) N (ell N)
                  (loopMasterProfile (ell N) ψ hψ)) (gibbsMeasure P N),
                ∃ hD : Integrable (fun X : Configuration N =>
                    fluctIntegral (fun u => deriv (loopMasterProfile (ell N) ψ hψ).val
                      (u / (ell N).val)) N X.val) (gibbsMeasure P N),
                  variance (gibbsMeasure P N) _ hL + variance (gibbsMeasure P N) _ hD ≤
                    ENNReal.ofReal (C * (((N : ℝ) * (ell N).val) ^ (2 * τ) *
                      ((N : ℝ) * (ell N).val +
                        ((N : ℝ) * (ell N).val) ^ (2 * (1 - P.val.2 + α))))) ∧
                  ∀ u : ℝ → ℝ, Continuous u → ∀ M : ℝ, 0 ≤ M → (∀ y, |u y| ≤ M) →
                    |(-(cltK N (ell N) ^ (-1 + P.val.2 / 2))) *
                      gibbsCov (gibbsMeasure P N)
                        (fun X => u (cltStat P N (ell N)
                          (cltScaledFun hρ (ell N) (cltDelta_pos P N (ell N))
                            ⟨periodizedProfile p (observationLength (ell N)),
                              periodizedProfileL2 p (ell N)⟩) X))
                        (cltRemainder P N (ell N) (loopMasterProfile (ell N) ψ hψ))| ≤
                      C * M * ((N : ℝ) * (ell N).val) ^
                        (max ((P.val.2 - 1) / 2) (α - P.val.2 / 2) + τ) :=
  Internal.clt_error2_of_input (Internal.aPrioriConclusion_of_externals hBE hPL)
    (Internal.errorTwoLoopVarianceInput_of_varAlVarianceInput
      (Internal.varAlVarianceInput_of_externals hBE hPL)) hPL P p α d hρ τ hτ

end Riesz1
