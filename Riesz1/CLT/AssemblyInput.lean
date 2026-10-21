/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.Identity
public import Riesz1.CLT.Smoothing
public import Riesz1.Variance.QuantitativeVarianceUniformConclusion
public import Riesz1.Frozen.External.PrekopaLeindler

/-!
# Conditional inputs of the central limit theorem assembly

The assembly `Riesz1.Internal.central_limit_theorem_of_inputs` (`Riesz1/CLT/Assembly.lean`) takes
the conclusions of three results of the paper as explicit hypotheses. This file states faithful
copies of these conclusions.

* `AssemblyErrorOneConclusion`: the bound `|Error¹_N(u)| ≤ C ‖u'‖∞ K^{s/2-1+τ} δ^{-2-α-τ}` of
  the first error bound in the proof of Theorem 3 (`errorOne_conclusion_of_facts`,
  `Riesz1/CLT/ErrorOneChain.lean`). Its integrand is `errorOneStein`, written out here as the
  integral of `clt_identity`.
* `AssemblyErrorTwoConclusion`: the bound `|Error²_N(u)| ≤ C ‖u‖∞ K^{max((s-1)/2,α-s/2)+τ}` of
  the second error bound in the proof of Theorem 3, with
  `Error²_N(u) = -K^{-1+s/2} Cov(u(G_N), B_N)` as in `clt_identity`.
* `AssemblyVarianceConclusion beta s`: the body of `Riesz1.quantitative_variance` (Theorem 2),
  copied from `Riesz1/CLT/MainConclusions.lean`.

The uniform variance conclusion `Riesz1.Internal.QuantitativeVarianceUniformConclusion` is used
directly.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal BoundedContinuousFunction

namespace Riesz1.Internal

/-- **First error bound in the proof of Theorem 3.** For every parameters `P`, profile `p`, exponent
`α`, test data `d` and mollifier `ρ`, there is `τ₀ > 0` such that for every `0 < τ < τ₀` there are
`C, K₀ > 0` with the following property. For every admissible scale sequence `ℓ` and particle
number `N` with `K = Nℓ_N ≥ K₀`, every transport `ψ` of the regularized profile, every `σ` with
`σ² = σ_reg²`, and every `C¹` function `u` with bounded `u` and `u'`,
`|E[u'(G_N) (K⁻¹ Σ_i q_N(x_i/ℓ) - σ²)]| ≤ C ‖u'‖∞ K^{s/2-1+τ} δ^{-2-α-τ}`. The constant does not
depend on `ψ`, `σ`, `u`, `N` or `ℓ`. -/
def AssemblyErrorOneConclusion : Prop :=
  ∀ (P : Parameters) (p : Profile) (α : ℝ) (d : TestData) {ρ : ℝ → ℝ} (hρ : IsMollifier ρ),
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τ : ℝ, 0 < τ → τ < τ₀ →
      ∃ C K₀ : ℝ, 0 < C ∧ 0 < K₀ ∧
        ∀ ell : Scales, Admissible P p ell α d → ∀ N : ℕ+, K₀ ≤ (N : ℝ) * (ell N).val →
          ∀ (ψ : Circle (loopMasterLength (ell N)) → ℝ)
            (hψ : ContDiff ℝ ∞ (fun u : ℝ => ψ (u : Circle (loopMasterLength (ell N)))))
            (_htr : ∀ k : ℤ, coeff (loopMasterLength (ell N))
              ⟨(fun z => (ψ z : ℂ)), complexL2Integrable _ _ (loopMasterLengthTest _ ψ hψ).property⟩ k =
              transportCoeffs P (loopMasterLength (ell N))
                (loopMasterLengthTest _ (cltReg hρ P N (ell N)
                  ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩)
                  (cltReg_contDiff hρ P N (ell N)
                    ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩)) k)
            (σ : ℝ)
            (_hσV : ENNReal.ofReal (σ ^ 2) = cltVariance P (ell N)
              ⟨fun x => (cltScaledLift hρ (ell N) (cltDelta_pos P N (ell N))
                ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ x : ℂ),
                cltScaledLift_memLp hρ (ell N) (cltDelta_pos P N (ell N))
                  ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩⟩)
            (u : ℝ → ℝ), ContDiff ℝ 1 u → (∃ B : ℝ, ∀ x, |u x| ≤ B) → ∀ M : ℝ,
            (∀ x, |deriv u x| ≤ M) →
            |∫ X, deriv u (cltStat P N (ell N) (cltScaledFun hρ (ell N) (cltDelta_pos P N (ell N))
                ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩) X) *
              ((cltK N (ell N))⁻¹ * cltPairingSum (ell N) (loopMasterProfile (ell N) ψ hψ)
                (cltRegLine hρ P N (ell N)
                  ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩) X
                - σ ^ 2)
              ∂(gibbsMeasure P N)| ≤
              C * M * (cltK N (ell N)) ^ (P.val.2 / 2 - 1 + τ) * (cltDelta P N (ell N)) ^ (-2 - α - τ)

/-- **Second error bound in the proof of Theorem 3.** For every parameters `P`, profile `p`,
exponent `α`, test data `d` and mollifier `ρ`, there is `τ₀ > 0` such that for every `0 < τ < τ₀`
there are `C, K₀ > 0` with the following property. For every admissible scale sequence `ℓ` and
particle number `N` with `K = Nℓ_N ≥ K₀`, every transport `ψ` of the regularized profile, and every
`C¹` function `u` bounded by `B`, `|Error²_N(u)| ≤ C B K^{max((s-1)/2, α-s/2)+τ}`, where
`Error²_N(u) = -K^{-1+s/2} Cov(u(G_N), B_N)`. The constant does not depend on `ψ`, `u`, `N` or `ℓ`. -/
def AssemblyErrorTwoConclusion : Prop :=
  ∀ (P : Parameters) (p : Profile) (α : ℝ) (d : TestData) {ρ : ℝ → ℝ} (hρ : IsMollifier ρ),
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τ : ℝ, 0 < τ → τ < τ₀ →
      ∃ C K₀ : ℝ, 0 < C ∧ 0 < K₀ ∧
        ∀ ell : Scales, Admissible P p ell α d → ∀ N : ℕ+, K₀ ≤ (N : ℝ) * (ell N).val →
          ∀ (ψ : Circle (loopMasterLength (ell N)) → ℝ)
            (hψ : ContDiff ℝ ∞ (fun u : ℝ => ψ (u : Circle (loopMasterLength (ell N)))))
            (_htr : ∀ k : ℤ, coeff (loopMasterLength (ell N))
              ⟨(fun z => (ψ z : ℂ)), complexL2Integrable _ _ (loopMasterLengthTest _ ψ hψ).property⟩ k =
              transportCoeffs P (loopMasterLength (ell N))
                (loopMasterLengthTest _ (cltReg hρ P N (ell N)
                  ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩)
                  (cltReg_contDiff hρ P N (ell N)
                    ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩)) k)
            (u : ℝ → ℝ), ContDiff ℝ 1 u → ∀ B : ℝ, (∀ x, |u x| ≤ B) →
            |(-(cltK N (ell N) ^ (-1 + P.val.2 / 2))) *
              gibbsCov (gibbsMeasure P N)
                (fun X => u (cltStat P N (ell N) (cltScaledFun hρ (ell N) (cltDelta_pos P N (ell N))
                  ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩) X))
                (cltRemainder P N (ell N) (loopMasterProfile (ell N) ψ hψ))| ≤
              C * B * (cltK N (ell N)) ^ (max ((P.val.2 - 1) / 2) (α - P.val.2 / 2) + τ)

/-- **Theorem 2.** The conclusion of
`Riesz1.quantitative_variance` for the parameters `(beta, s)`. The body is copied symbol for symbol
from `Riesz1/CLT/MainConclusions.lean`, where it is the `Prop` `QuantitativeVarianceConclusion`. -/
def AssemblyVarianceConclusion (beta s : ℝ) (hbeta : 0 < beta) (hs : 0 < s) (hs1 : s < 1) :
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

end Riesz1.Internal

end
end
