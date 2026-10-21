/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.ErrorTwoFinalDerivative

/-!
# The complete loop-error theorem, conditional on its two inputs

The second error bound in the proof of Theorem 3: both variances and the second Stein error.
The proof inputs are exactly the a-priori conclusion and the
loop-variance assertion, together with the Prékopa–Leindler inequality
`External.PrekopaLeindler`, used for loop square integrability. Every coefficient precedes the scale
sequence. The separation-free derivative decomposition includes all
initial observation circles and the endpoint `α = s - 1`.
-/

public section

open MeasureTheory
open scoped ContDiff ENNReal

namespace Riesz1.Internal

/-- Every assertion of the second error bound in the proof of Theorem 3, conditional only on the
a-priori and loop-variance conclusions. This holds for every
positive loss, every continuous bounded test, and `K₀ = 1`. -/
theorem clt_error2_of_input (hAP : APrioriConclusion) (hLoop : ErrorTwoLoopVarianceInput)
    (hPL : External.PrekopaLeindler) (P : Parameters) (p : Profile) (α : ℝ)
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
                        (max ((P.val.2 - 1) / 2) (α - P.val.2 / 2) + τ) := by
  obtain ⟨CL, hCL, hloop⟩ := clt_error2_loop_of_input hLoop P p α d ρ hρ τ hτ
  obtain ⟨CD, hCD, hder⟩ := errorTwo_derivative_of_input hAP P p α d hρ τ hτ
  let V := CL + CD
  let E := 2 * Real.sqrt (2 * (P.val.1 ^ 2 + 1) * V)
  let C := V + E + 1
  have hV : 0 < V := by dsimp [V]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hVC : V ≤ C := by dsimp [C]; linarith
  have hEC : E ≤ C := by dsimp [C]; linarith
  refine ⟨C, 1, hC, one_pos, fun ell hadm N hK ψ hψ htr => ?_⟩
  obtain ⟨hL, hLV⟩ := hloop ell hadm N hK ψ hψ htr
  obtain ⟨hD, hDV⟩ := hder ell hadm N hK ψ hψ htr
  let R := ((N : ℝ) * (ell N).val) ^ (2 * τ) *
    ((N : ℝ) * (ell N).val + ((N : ℝ) * (ell N).val) ^ (2 * (1 - P.val.2 + α)))
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hsum : variance (gibbsMeasure P N) _ hL + variance (gibbsMeasure P N) _ hD ≤
      ENNReal.ofReal (V * R) := by
    calc
      _ ≤ ENNReal.ofReal (CL * R) + ENNReal.ofReal (CD * R) := add_le_add hLV hDV
      _ = _ := by
        rw [← ENNReal.ofReal_add (mul_nonneg hCL.le hR) (mul_nonneg hCD.le hR)]
        congr 1
        dsimp [V]
        ring
  refine ⟨hL, hD, hsum.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right hVC hR)), fun u hu M hM hub => ?_⟩
  have hG : AEStronglyMeasurable
      (cltStat P N (ell N) (cltScaledFun hρ (ell N) (cltDelta_pos P N (ell N))
        ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩))
      (gibbsMeasure P N) :=
    (continuous_cltStat P N (ell N) (cltScaledFun_contDiff hρ P N (ell N) _).continuous).aestronglyMeasurable
  have hv := clt_error2_of_variance_bound hPL P N (ell N) hK
    (loopMasterProfile (ell N) ψ hψ) hψ V τ α hV.le ⟨hL, hD, hsum⟩ hG hu hM hub
  exact hv.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hEC hM) (by positivity))

end Riesz1.Internal
