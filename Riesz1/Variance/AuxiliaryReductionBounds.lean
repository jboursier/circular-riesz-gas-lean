/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.AuxiliaryReductionIdentity
public import Riesz1.Variance.AuxiliaryReductionBell

/-!
# Uniform probabilistic reduction of the variance error

Proposition 5.6, with the Bell estimate supplied. The
remaining terms are the analytic smoothing error and transport energy,
the microscopic error variance, and the derivative-statistic variance.
The constant here precedes every profile and every scale. This is an
intermediate estimate, not the full rate theorem.
-/

public section

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace Riesz1.Internal

/-- All probabilistic steps of the loop reduction, for every real `L²`
profile with finite Sobolev variance. The sole external hypotheses are
the Bakry–Émery criterion `External.BakryEmery` and the Prékopa–Leindler
inequality `External.PrekopaLeindler`. The analytic rates are not hypotheses. -/
theorem auxiliary_reduction_bound (hBE : External.BakryEmery)
    (hPL : External.PrekopaLeindler) (P : Parameters) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ+) (ℓ : Scale), 1 ≤ cltK N ℓ →
      ∀ (ρ : ℝ → ℝ) (hρ : IsMollifier ρ)
        (ξ : {f : Circle (loopMasterLength ℓ) → ℝ //
          MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength ℓ))}),
        scaledVariance P ℓ ξ ≠ ⊤ →
      ∀ (ψh : Circle (loopMasterLength ℓ) → ℝ)
        (hψh : ContDiff ℝ ∞ (fun u : ℝ => ψh (u : Circle (loopMasterLength ℓ)))),
        (∀ k : ℤ, coeff (loopMasterLength ℓ)
          ⟨(fun z => (ψh z : ℂ)), complexL2Integrable _ _ (loopMasterLengthTest _ ψh hψh).property⟩ k =
          transportCoeffs P (loopMasterLength ℓ)
            (loopMasterLengthTest _ (mixedRegCircle hρ N ℓ ξ) (mixedRegCircle_contDiff hρ N ℓ ξ)) k) →
      let μ := gibbsMeasure P N
      let E := mixedStat P N ℓ (subCircleL2 ξ (mixedReg hρ N ℓ ξ))
      let A := loopOnConfiguration (parametersExponent P) N ℓ (loopMasterProfile ℓ ψh hψh)
      let Q := fun X : Configuration N =>
        fluctIntegral (fun u => deriv (loopMasterProfile ℓ ψh hψh).val (u / ℓ.val)) N X.val
      ∃ hF : Integrable (mixedStat P N ℓ ξ) μ,
        variance μ (mixedStat P N ℓ ξ) hF ≠ ⊤ ∧
        |(variance μ (mixedStat P N ℓ ξ) hF).toReal -
            cltK N ℓ ^ P.val.2 * (scaledVariance P ℓ ξ).toReal| ≤
          3 * gibbsCov μ E E +
          3 * cltK N ℓ ^ (2 * P.val.2 - 2) * P.val.1 ^ 2 * gibbsCov μ A A +
          3 * cltK N ℓ ^ (2 * P.val.2 - 2) * gibbsCov μ Q Q +
          cltK N ℓ ^ P.val.2 *
            (scaledVariance P ℓ (subCircleL2 ξ (mixedReg hρ N ℓ ξ))).toReal +
          C * cltK N ℓ ^ (2 * P.val.2 - 1) *
            bellEnergy ℓ.val (loopMasterProfile ℓ ψh hψh).val := by
  obtain ⟨B, hB, hbell⟩ := auxiliary_hessian_expectation hBE hPL P
  refine ⟨P.val.1 * B + 1, by positivity [P.property.1], ?_⟩
  intro N ℓ hK ρ hρ ξ hσ ψh hψh htr
  dsimp only
  obtain ⟨hF, hfin, hv⟩ :=
    auxiliary_reduction_preliminary P N ℓ hρ ξ ψh hψh htr hPL hK hσ
  refine ⟨hF, hfin, hv.trans ?_⟩
  have hb := hbell N ℓ (loopMasterProfile ℓ ψh hψh) hK hψh
  have hC : 0 ≤ P.val.1 * cltK N ℓ ^ (2 * P.val.2 - 2) :=
    mul_nonneg P.property.1.le (Real.rpow_nonneg (cltK_pos N ℓ).le _)
  have hr : cltK N ℓ ^ (2 * P.val.2 - 2) * cltK N ℓ =
      cltK N ℓ ^ (2 * P.val.2 - 1) := by
    conv_lhs => arg 2; rw [← Real.rpow_one (cltK N ℓ)]
    rw [← Real.rpow_add (cltK_pos N ℓ)]
    congr 1
    ring
  have hscaled := mul_le_mul_of_nonneg_left hb hC
  rw [mul_assoc B (N : ℝ) ℓ.val] at hscaled
  change P.val.1 * cltK N ℓ ^ (2 * P.val.2 - 2) * |(N : ℝ) ^ (-P.val.2) *
      ∫ X : Configuration N, hessFluctExpansion P.val.2 (N : ℕ)
        (loopScaleField ℓ.val (loopMasterProfile ℓ ψh hψh).val) X.val ∂gibbsMeasure P N| ≤
      P.val.1 * cltK N ℓ ^ (2 * P.val.2 - 2) *
        (B * cltK N ℓ * bellEnergy ℓ.val (loopMasterProfile ℓ ψh hψh).val) at hscaled
  have he : P.val.1 * cltK N ℓ ^ (2 * P.val.2 - 2) *
      (B * cltK N ℓ * bellEnergy ℓ.val (loopMasterProfile ℓ ψh hψh).val) =
      P.val.1 * B * cltK N ℓ ^ (2 * P.val.2 - 1) *
        bellEnergy ℓ.val (loopMasterProfile ℓ ψh hψh).val := by
    calc
      _ = P.val.1 * B * (cltK N ℓ ^ (2 * P.val.2 - 2) * cltK N ℓ) *
          bellEnergy ℓ.val (loopMasterProfile ℓ ψh hψh).val := by ring
      _ = _ := by rw [hr]
  rw [he] at hscaled
  unfold bellEnergy at hscaled ⊢
  linarith only [hscaled]

end Riesz1.Internal

end
