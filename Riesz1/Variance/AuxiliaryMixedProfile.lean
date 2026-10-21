/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.AuxiliaryMixedProfileBridge
public import Riesz1.Kernel.AdmissibilityRegularityConsequences

/-!
# The mixed mean-field variance for profiles (part of Proposition 5.6)

This is `Riesz1.mixed_mean_field_variance` for the periodization `ξ` of a profile `p`
on the circle of length `ℓ⁻¹`. Its variance `σ_ℓ²(ξ)` is written as
`Riesz1.circleVariance P p ℓ`, by the bridge `Riesz1.scaledVariance_periodizedProfile`.

The variances `σ_ℓ²(ξ_h)` and `σ_ℓ²(ξ - ξ_h)` are not profiles, so they stay as
`Riesz1.scaledVariance`.

* `Riesz1.mixed_mean_field_variance_profile_of_ne_top` takes every profile whose circle variance
  at `ℓ` is finite. This is the more general form, with finiteness as the only assumption on the
  profile.
* `Riesz1.mixed_mean_field_variance_profile` takes an admissible profile and an admissible scale
  `ℓ = ell M` of the `Riesz1.Admissible` predicate. It derives finiteness from
  `Riesz1.admissible_circleVariance_finite`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology ComplexConjugate Real
open scoped ContDiff ENNReal

namespace Riesz1

/-- The mixed mean-field variance identities of Proposition 5.6 for the periodization of a
profile `p` at a scale `ℓ`, with `σ_ℓ²(ξ)` written as `circleVariance P p ℓ`. Here
`ξ` is the periodization `periodizedProfile p (observationLength ℓ)` (given by `hξ`), `ξ_h` is its
regularization at `h = K⁻¹`, and `ψ_h` is any smooth mean-zero transport of `ξ_h`. The only
admissibility input is the finiteness `circleVariance P p ℓ ≠ ⊤`. -/
theorem mixed_mean_field_variance_profile_of_ne_top (hPL : External.PrekopaLeindler)
    (P : Parameters) (N : ℕ+) (p : Profile) (ℓ : Scale) (hK : 1 ≤ cltK N ℓ)
    {ρ : ℝ → ℝ} (hρ : IsMollifier ρ)
    (ξ : {f : Circle (loopMasterLength ℓ) → ℝ //
      MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength ℓ))})
    (hξ : ξ.val = periodizedProfile p (observationLength ℓ))
    (hσ : circleVariance P p ℓ ≠ ⊤)
    (ψh : Circle (loopMasterLength ℓ) → ℝ)
    (hψh : ContDiff ℝ ∞ (fun u : ℝ => ψh (u : Circle (loopMasterLength ℓ))))
    (htr : ∀ k : ℤ, coeff (loopMasterLength ℓ)
      ⟨(fun z => (ψh z : ℂ)), complexL2Integrable _ _ (loopMasterLengthTest _ ψh hψh).property⟩ k =
      transportCoeffs P (loopMasterLength ℓ)
        (loopMasterLengthTest _ (mixedRegCircle hρ N ℓ ξ) (mixedRegCircle_contDiff hρ N ℓ ξ)) k) :
    (MemLp (mixedStat P N ℓ ξ) 2 (gibbsMeasure P N) ∧
      MemLp (mixedOp P N ℓ ψh hψh) 2 (gibbsMeasure P N)) ∧
    gibbsCov (gibbsMeasure P N) (mixedStat P N ℓ ξ) (mixedStat P N ℓ ξ) =
      2 * gibbsCov (gibbsMeasure P N) (mixedStat P N ℓ ξ) (mixedOp P N ℓ ψh hψh) -
        gibbsCov (gibbsMeasure P N) (mixedOp P N ℓ ψh hψh) (mixedOp P N ℓ ψh hψh) +
        gibbsCov (gibbsMeasure P N) (fun X => mixedStat P N ℓ ξ X - mixedOp P N ℓ ψh hψh X)
          (fun X => mixedStat P N ℓ ξ X - mixedOp P N ℓ ψh hψh X) ∧
    (scaledVariance P ℓ (subCircleL2 ξ (mixedReg hρ N ℓ ξ)) ≠ ⊤ ∧
      gibbsCov (gibbsMeasure P N) (mixedStat P N ℓ ξ) (mixedOp P N ℓ ψh hψh) =
        (cltK N ℓ ^ P.val.2 / 2) * ((circleVariance P p ℓ).toReal +
          (scaledVariance P ℓ (mixedReg hρ N ℓ ξ)).toReal -
          (scaledVariance P ℓ (subCircleL2 ξ (mixedReg hρ N ℓ ξ))).toReal)) ∧
    2 * gibbsCov (gibbsMeasure P N) (mixedStat P N ℓ ξ) (mixedOp P N ℓ ψh hψh) -
        gibbsCov (gibbsMeasure P N) (mixedOp P N ℓ ψh hψh) (mixedOp P N ℓ ψh hψh) =
      cltK N ℓ ^ P.val.2 * (circleVariance P p ℓ).toReal -
        cltK N ℓ ^ P.val.2 * (scaledVariance P ℓ (subCircleL2 ξ (mixedReg hρ N ℓ ξ))).toReal -
        P.val.1 * cltK N ℓ ^ (2 * P.val.2 - 2) *
          ((N : ℝ) ^ (-P.val.2) * ∫ X : Configuration N,
            hessFluctExpansion P.val.2 (N : ℕ)
              (loopScaleField ℓ.val (loopMasterProfile ℓ ψh hψh).val) X.val ∂(gibbsMeasure P N)) -
        cltK N ℓ ^ (2 * P.val.2 - 1) * ∫ v in (0 : ℝ)..ℓ.val⁻¹,
          deriv (loopMasterProfile ℓ ψh hψh).val v ^ 2 := by
  -- The profile ξ is the bridge element, so its variance is the circle variance.
  have hξe : ξ = ⟨periodizedProfile p (observationLength ℓ), periodizedProfileL2 p ℓ⟩ :=
    Subtype.ext hξ
  have hbr : scaledVariance P ℓ ξ = circleVariance P p ℓ := by
    rw [hξe]
    exact scaledVariance_periodizedProfile P p ℓ
  have hσ' : scaledVariance P ℓ ξ ≠ ⊤ := by
    rw [hbr]
    exact hσ
  have key := mixed_mean_field_variance hPL P N ℓ hK hρ ξ hσ' ψh hψh htr
  rw [hbr] at key
  exact key

/-- The mixed mean-field variance identities of Proposition 5.6 for the periodization of an
admissible profile at an admissible scale. The scale is `ℓ = ell M` for the admissible
sequence `ell` of `Riesz1.Admissible`, and the finiteness of `σ_ℓ²(ξ)` comes from
`Riesz1.admissible_circleVariance_finite`. Every `σ_ℓ²(ξ)` is `circleVariance P p ℓ`. -/
theorem mixed_mean_field_variance_profile (hPL : External.PrekopaLeindler)
    (P : Parameters) (N : ℕ+) (p : Profile) (ell : Scales) (α : ℝ) (d : TestData)
    (hadm : Admissible P p ell α d) (M : ℕ+) (ℓ : Scale) (hℓ : ℓ = ell M)
    (hK : 1 ≤ cltK N ℓ) {ρ : ℝ → ℝ} (hρ : IsMollifier ρ)
    (ξ : {f : Circle (loopMasterLength ℓ) → ℝ //
      MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength ℓ))})
    (hξ : ξ.val = periodizedProfile p (observationLength ℓ))
    (ψh : Circle (loopMasterLength ℓ) → ℝ)
    (hψh : ContDiff ℝ ∞ (fun u : ℝ => ψh (u : Circle (loopMasterLength ℓ))))
    (htr : ∀ k : ℤ, coeff (loopMasterLength ℓ)
      ⟨(fun z => (ψh z : ℂ)), complexL2Integrable _ _ (loopMasterLengthTest _ ψh hψh).property⟩ k =
      transportCoeffs P (loopMasterLength ℓ)
        (loopMasterLengthTest _ (mixedRegCircle hρ N ℓ ξ) (mixedRegCircle_contDiff hρ N ℓ ξ)) k) :
    (MemLp (mixedStat P N ℓ ξ) 2 (gibbsMeasure P N) ∧
      MemLp (mixedOp P N ℓ ψh hψh) 2 (gibbsMeasure P N)) ∧
    gibbsCov (gibbsMeasure P N) (mixedStat P N ℓ ξ) (mixedStat P N ℓ ξ) =
      2 * gibbsCov (gibbsMeasure P N) (mixedStat P N ℓ ξ) (mixedOp P N ℓ ψh hψh) -
        gibbsCov (gibbsMeasure P N) (mixedOp P N ℓ ψh hψh) (mixedOp P N ℓ ψh hψh) +
        gibbsCov (gibbsMeasure P N) (fun X => mixedStat P N ℓ ξ X - mixedOp P N ℓ ψh hψh X)
          (fun X => mixedStat P N ℓ ξ X - mixedOp P N ℓ ψh hψh X) ∧
    (scaledVariance P ℓ (subCircleL2 ξ (mixedReg hρ N ℓ ξ)) ≠ ⊤ ∧
      gibbsCov (gibbsMeasure P N) (mixedStat P N ℓ ξ) (mixedOp P N ℓ ψh hψh) =
        (cltK N ℓ ^ P.val.2 / 2) * ((circleVariance P p ℓ).toReal +
          (scaledVariance P ℓ (mixedReg hρ N ℓ ξ)).toReal -
          (scaledVariance P ℓ (subCircleL2 ξ (mixedReg hρ N ℓ ξ))).toReal)) ∧
    2 * gibbsCov (gibbsMeasure P N) (mixedStat P N ℓ ξ) (mixedOp P N ℓ ψh hψh) -
        gibbsCov (gibbsMeasure P N) (mixedOp P N ℓ ψh hψh) (mixedOp P N ℓ ψh hψh) =
      cltK N ℓ ^ P.val.2 * (circleVariance P p ℓ).toReal -
        cltK N ℓ ^ P.val.2 * (scaledVariance P ℓ (subCircleL2 ξ (mixedReg hρ N ℓ ξ))).toReal -
        P.val.1 * cltK N ℓ ^ (2 * P.val.2 - 2) *
          ((N : ℝ) ^ (-P.val.2) * ∫ X : Configuration N,
            hessFluctExpansion P.val.2 (N : ℕ)
              (loopScaleField ℓ.val (loopMasterProfile ℓ ψh hψh).val) X.val ∂(gibbsMeasure P N)) -
        cltK N ℓ ^ (2 * P.val.2 - 1) * ∫ v in (0 : ℝ)..ℓ.val⁻¹,
          deriv (loopMasterProfile ℓ ψh hψh).val v ^ 2 := by
  subst hℓ
  exact mixed_mean_field_variance_profile_of_ne_top hPL P N p (ell M) hK hρ ξ hξ
    (admissible_circleVariance_finite P p ell α d hadm M).ne ψh hψh htr

end Riesz1

end
end
