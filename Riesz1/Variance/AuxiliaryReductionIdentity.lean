/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.AuxiliaryMixedProfile
public import Riesz1.ToMathlib.VarianceThreeTerm
public import Riesz1.Variance.VarAlPiecesLoopMemLp
import all Riesz1.Variance.LoopIBPUniform
import all Riesz1.Variance.LoopForce
import all Riesz1.Variance.LoopIBPMoments

/-!
# Exact remainder for the reduced variance expansion

The exact identities in the proof of Proposition 5.6, before
the quantitative estimates. The original statistic remains in the
covariance. Smoothing uses `mixedReg` at `h = (Nℓ)⁻¹` and its transport
is identified by the Fourier coefficients. No new analytic
objects or conditional proof inputs are introduced.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1.Internal

/-- The differentiated smooth transport statistic is square integrable.
No quantitative derivative estimate is needed for this certificate. -/
theorem auxiliary_derivative_stat_memLp (P : Parameters) (N : ℕ+) (ℓ : Scale)
    (ψ : LoopScaleProfile ℓ.val) (hψ : ContDiff ℝ ∞ ψ.val) :
    MemLp (fun X : Configuration N =>
      fluctIntegral (fun u => deriv ψ.val (u / ℓ.val)) N X.val) 2 (gibbsMeasure P N) := by
  have hc : Continuous (fun u => deriv ψ.val (u / ℓ.val)) :=
    (hψ.continuous_deriv (by simp)).comp (continuous_id.div_const _)
  have hp : Function.Periodic (fun u => deriv ψ.val (u / ℓ.val)) 1 :=
    periodic_div_scale (deriv_periodic_of ψ.property.1)
  have hL := memLp_lift_of_continuous hc hp
  have heq : (fun X : Configuration N =>
      fluctIntegral (fun u => deriv ψ.val (u / ℓ.val)) N X.val) =
      fun X => fluctuation ⟨hp.lift, hL.integrable one_le_two⟩ X := by
    funext X
    exact (fluctuation_eq_fluctIntegral hc hp X).symm
  rw [heq]
  exact memLp_fluctuation P N hL

/-- Linearity of the existing profile statistic. -/
theorem auxiliary_mixedStat_sub (P : Parameters) (N : ℕ+) (ℓ : Scale)
    (f g : {f : Circle (loopMasterLength ℓ) → ℝ //
      MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength ℓ))})
    (X : Configuration N) :
    mixedStat P N ℓ (subCircleL2 f g) X = mixedStat P N ℓ f X - mixedStat P N ℓ g X := by
  exact fluctuation_sub_lift _ _ _ _ X

/-- The existing statistic agrees with the lifted integral formula, also
for nonsmooth `L²` tests. -/
theorem auxiliary_mixedStat_lift (P : Parameters) (N : ℕ+) (ℓ : Scale)
    (f : {f : Circle (loopMasterLength ℓ) → ℝ //
      MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength ℓ))})
    (X : Configuration N) :
    mixedStat P N ℓ f X =
      fluctIntegral (fun u => f.val ((u / ℓ.val : ℝ) : Circle (loopMasterLength ℓ))) N X.val := by
  unfold mixedStat
  rw [fluctuation_eq_fluctIntegral_lift]
  simp only [loopMasterPullback_coe, loopMasterLength, div_eq_mul_inv]

variable (P : Parameters) (N : ℕ+) (ℓ : Scale)
    {ρ : ℝ → ℝ} (hρ : IsMollifier ρ)
    (ξ : {f : Circle (loopMasterLength ℓ) → ℝ //
      MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength ℓ))})
    (ψh : Circle (loopMasterLength ℓ) → ℝ)
    (hψh : ContDiff ℝ ∞ (fun u : ℝ => ψh (u : Circle (loopMasterLength ℓ))))
    (htr : ∀ k : ℤ, coeff (loopMasterLength ℓ)
      ⟨(fun z => (ψh z : ℂ)), complexL2Integrable _ _ (loopMasterLengthTest _ ψh hψh).property⟩ k =
      transportCoeffs P (loopMasterLength ℓ)
        (loopMasterLengthTest _ (mixedRegCircle hρ N ℓ ξ) (mixedRegCircle_contDiff hρ N ℓ ξ)) k)

include htr

/-- The master remainder in the proof of Proposition 5.6, pointwise for
the original singular statistic. It includes `N = 1`. -/
theorem auxiliary_remainder_pointwise (X : Configuration N) :
    mixedStat P N ℓ ξ X - mixedOp P N ℓ ψh hψh X =
      mixedStat P N ℓ (subCircleL2 ξ (mixedReg hρ N ℓ ξ)) X -
      cltK N ℓ ^ (P.val.2 - 1) *
        (P.val.1 * loopOnConfiguration (parametersExponent P) N ℓ (loopMasterProfile ℓ ψh hψh) X -
          fluctIntegral (fun u => deriv (loopMasterProfile ℓ ψh hψh).val (u / ℓ.val)) N X.val) := by
  have hm := loop_equations_master P N ℓ (mixedRegCircle hρ N ℓ ξ) ψh
    (mixedRegCircle_contDiff hρ N ℓ ξ) hψh htr X.val (fun _ _ hij => coe_sub_ne_zero X hij)
  change mixedOp P N ℓ ψh hψh X -
    fluctIntegral (fun u => (mixedReg hρ N ℓ ξ).val
      ((u / ℓ.val : ℝ) : Circle (loopMasterLength ℓ))) N X.val = _ at hm
  rw [← auxiliary_mixedStat_lift P N ℓ (mixedReg hρ N ℓ ξ) X] at hm
  change mixedOp P N ℓ ψh hψh X - mixedStat P N ℓ (mixedReg hρ N ℓ ξ) X =
    cltK N ℓ ^ (P.val.2 - 1) *
      (P.val.1 * loopOnConfiguration (parametersExponent P) N ℓ (loopMasterProfile ℓ ψh hψh) X -
        fluctIntegral (fun u => deriv (loopMasterProfile ℓ ψh hψh).val (u / ℓ.val)) N X.val) at hm
  rw [auxiliary_mixedStat_sub]
  linarith only [hm]

/-- Subadditivity applied to the exact master remainder. All three
variances are finite centered moments of the objects at hand. -/
theorem auxiliary_remainder_variance (hPL : External.PrekopaLeindler) :
    gibbsCov (gibbsMeasure P N)
        (fun X => mixedStat P N ℓ ξ X - mixedOp P N ℓ ψh hψh X)
        (fun X => mixedStat P N ℓ ξ X - mixedOp P N ℓ ψh hψh X) ≤
      3 * gibbsCov (gibbsMeasure P N)
        (mixedStat P N ℓ (subCircleL2 ξ (mixedReg hρ N ℓ ξ)))
        (mixedStat P N ℓ (subCircleL2 ξ (mixedReg hρ N ℓ ξ))) +
      3 * cltK N ℓ ^ (2 * P.val.2 - 2) * P.val.1 ^ 2 *
        gibbsCov (gibbsMeasure P N)
          (loopOnConfiguration (parametersExponent P) N ℓ (loopMasterProfile ℓ ψh hψh))
          (loopOnConfiguration (parametersExponent P) N ℓ (loopMasterProfile ℓ ψh hψh)) +
      3 * cltK N ℓ ^ (2 * P.val.2 - 2) *
        gibbsCov (gibbsMeasure P N)
          (fun X => fluctIntegral (fun u => deriv (loopMasterProfile ℓ ψh hψh).val (u / ℓ.val)) N X.val)
          (fun X => fluctIntegral (fun u => deriv (loopMasterProfile ℓ ψh hψh).val (u / ℓ.val)) N X.val) := by
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  have hE : MemLp (mixedStat P N ℓ (subCircleL2 ξ (mixedReg hρ N ℓ ξ))) 2
      (gibbsMeasure P N) :=
    memLp_fluctuation P N (memLp_real_of_complex (loopMasterPullback_memLp _ _))
  have hA : MemLp
      (loopOnConfiguration (parametersExponent P) N ℓ (loopMasterProfile ℓ ψh hψh)) 2
      (gibbsMeasure P N) := by
    obtain ⟨M, hM⟩ := loopScaleField_lipschitz (loopMasterProfile ℓ ψh hψh)
    exact memLp_loopFunctional_gibbs P hPL N P.property.2.1 P.property.2.2 hM
      (loopScaleField_periodic (loopMasterProfile ℓ ψh hψh).property.1)
  have hQ := auxiliary_derivative_stat_memLp P N ℓ (loopMasterProfile ℓ ψh hψh) hψh
  have hp : (cltK N ℓ ^ (P.val.2 - 1)) ^ 2 = cltK N ℓ ^ (2 * P.val.2 - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (cltK_pos N ℓ).le]
    congr 1
    ring
  have hv := centeredIntegral_three_le (gibbsMeasure P N) hE hA hQ
    (cltK N ℓ ^ (P.val.2 - 1)) P.val.1
  simp only [gibbsCov, ← pow_two]
  simp_rw [auxiliary_remainder_pointwise P N ℓ hρ ξ ψh hψh htr]
  simpa only [hp] using hv

/-- Exact variance error, combining both mixed identities. This is the
identity to which the estimates of Proposition 5.6 are applied. -/
theorem auxiliary_reduction_exact (hPL : External.PrekopaLeindler)
    (hK : 1 ≤ cltK N ℓ) (hσ : scaledVariance P ℓ ξ ≠ ⊤) :
    ∃ hF : Integrable (mixedStat P N ℓ ξ) (gibbsMeasure P N),
      variance (gibbsMeasure P N) (mixedStat P N ℓ ξ) hF ≠ ⊤ ∧
      (variance (gibbsMeasure P N) (mixedStat P N ℓ ξ) hF).toReal -
        cltK N ℓ ^ P.val.2 * (scaledVariance P ℓ ξ).toReal =
      gibbsCov (gibbsMeasure P N)
        (fun X => mixedStat P N ℓ ξ X - mixedOp P N ℓ ψh hψh X)
        (fun X => mixedStat P N ℓ ξ X - mixedOp P N ℓ ψh hψh X) -
      cltK N ℓ ^ P.val.2 * (scaledVariance P ℓ (subCircleL2 ξ (mixedReg hρ N ℓ ξ))).toReal -
      P.val.1 * cltK N ℓ ^ (2 * P.val.2 - 2) *
        ((N : ℝ) ^ (-P.val.2) * ∫ X : Configuration N,
          hessFluctExpansion P.val.2 (N : ℕ)
            (loopScaleField ℓ.val (loopMasterProfile ℓ ψh hψh).val) X.val ∂gibbsMeasure P N) -
      cltK N ℓ ^ (2 * P.val.2 - 1) *
        ∫ v in (0 : ℝ)..ℓ.val⁻¹, deriv (loopMasterProfile ℓ ψh hψh).val v ^ 2 := by
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  obtain ⟨⟨hF, _hT⟩, hsplit, _hcov, hmain⟩ :=
    mixed_mean_field_variance hPL P N ℓ hK hρ ξ hσ ψh hψh htr
  refine ⟨hF.integrable one_le_two, variance_ne_top_of_memLp _ hF, ?_⟩
  rw [variance_toReal_of_memLp _ hF]
  have hself : (∫ X, (mixedStat P N ℓ ξ X -
      ∫ Y, mixedStat P N ℓ ξ Y ∂gibbsMeasure P N) ^ 2 ∂gibbsMeasure P N) =
      gibbsCov (gibbsMeasure P N) (mixedStat P N ℓ ξ) (mixedStat P N ℓ ξ) := by
    simp only [gibbsCov, pow_two]
  rw [hself, hsplit, hmain]
  ring

/-- Reduction to the three quantitative estimates, with their exact
coefficients. This is valid for any real `L²` profile with finite Sobolev
variance. The microscopic variance, the derivative-statistic variance,
the Sobolev error and the two deterministic transport errors still need
their analytic rates to obtain the full statement of Proposition 5.6. -/
theorem auxiliary_reduction_preliminary (hPL : External.PrekopaLeindler)
    (hK : 1 ≤ cltK N ℓ) (hσ : scaledVariance P ℓ ξ ≠ ⊤) :
    let μ := gibbsMeasure P N
    let E := mixedStat P N ℓ (subCircleL2 ξ (mixedReg hρ N ℓ ξ))
    let A := loopOnConfiguration (parametersExponent P) N ℓ (loopMasterProfile ℓ ψh hψh)
    let Q := fun X : Configuration N =>
      fluctIntegral (fun u => deriv (loopMasterProfile ℓ ψh hψh).val (u / ℓ.val)) N X.val
    let H := (N : ℝ) ^ (-P.val.2) * ∫ X : Configuration N,
      hessFluctExpansion P.val.2 (N : ℕ)
        (loopScaleField ℓ.val (loopMasterProfile ℓ ψh hψh).val) X.val ∂μ
    let J := ∫ v in (0 : ℝ)..ℓ.val⁻¹, deriv (loopMasterProfile ℓ ψh hψh).val v ^ 2
    ∃ hF : Integrable (mixedStat P N ℓ ξ) μ,
      variance μ (mixedStat P N ℓ ξ) hF ≠ ⊤ ∧
      |(variance μ (mixedStat P N ℓ ξ) hF).toReal -
          cltK N ℓ ^ P.val.2 * (scaledVariance P ℓ ξ).toReal| ≤
        3 * gibbsCov μ E E +
        3 * cltK N ℓ ^ (2 * P.val.2 - 2) * P.val.1 ^ 2 * gibbsCov μ A A +
        3 * cltK N ℓ ^ (2 * P.val.2 - 2) * gibbsCov μ Q Q +
        cltK N ℓ ^ P.val.2 *
          (scaledVariance P ℓ (subCircleL2 ξ (mixedReg hρ N ℓ ξ))).toReal +
        P.val.1 * cltK N ℓ ^ (2 * P.val.2 - 2) * |H| +
        cltK N ℓ ^ (2 * P.val.2 - 1) * J := by
  dsimp only
  obtain ⟨hF, hfin, heq⟩ := auxiliary_reduction_exact P N ℓ hρ ξ ψh hψh htr hPL hK hσ
  refine ⟨hF, hfin, ?_⟩
  have hD : 0 ≤ gibbsCov (gibbsMeasure P N)
      (fun X => mixedStat P N ℓ ξ X - mixedOp P N ℓ ψh hψh X)
      (fun X => mixedStat P N ℓ ξ X - mixedOp P N ℓ ψh hψh X) :=
    integral_nonneg fun X => mul_self_nonneg _
  have hJ : 0 ≤ ∫ v in (0 : ℝ)..ℓ.val⁻¹,
      deriv (loopMasterProfile ℓ ψh hψh).val v ^ 2 :=
    intervalIntegral.integral_nonneg (inv_nonneg.mpr ℓ.property.1.le) (fun _ _ => sq_nonneg _)
  have hB : 0 ≤ cltK N ℓ ^ P.val.2 *
      (scaledVariance P ℓ (subCircleL2 ξ (mixedReg hρ N ℓ ξ))).toReal :=
    mul_nonneg (Real.rpow_nonneg (cltK_pos N ℓ).le _) ENNReal.toReal_nonneg
  have hC : 0 ≤ P.val.1 * cltK N ℓ ^ (2 * P.val.2 - 2) := by
    exact mul_nonneg P.property.1.le (Real.rpow_nonneg (cltK_pos N ℓ).le _)
  have hJ' : 0 ≤ cltK N ℓ ^ (2 * P.val.2 - 1) *
      ∫ v in (0 : ℝ)..ℓ.val⁻¹, deriv (loopMasterProfile ℓ ψh hψh).val v ^ 2 :=
    mul_nonneg (Real.rpow_nonneg (cltK_pos N ℓ).le _) hJ
  rw [heq]
  have habs (d b c j : ℝ) : |d - b - c - j| ≤ |d| + |b| + |c| + |j| := by
    calc
      _ ≤ |d - b - c| + |j| := abs_sub _ _
      _ ≤ (|d - b| + |c|) + |j| := by linarith only [abs_sub (d - b) c]
      _ ≤ _ := by linarith only [abs_sub d b]
  have hb := habs
    (gibbsCov (gibbsMeasure P N)
      (fun X => mixedStat P N ℓ ξ X - mixedOp P N ℓ ψh hψh X)
      (fun X => mixedStat P N ℓ ξ X - mixedOp P N ℓ ψh hψh X))
    (cltK N ℓ ^ P.val.2 * (scaledVariance P ℓ (subCircleL2 ξ (mixedReg hρ N ℓ ξ))).toReal)
    (P.val.1 * cltK N ℓ ^ (2 * P.val.2 - 2) *
      ((N : ℝ) ^ (-P.val.2) * ∫ X : Configuration N,
        hessFluctExpansion P.val.2 (N : ℕ)
          (loopScaleField ℓ.val (loopMasterProfile ℓ ψh hψh).val) X.val ∂gibbsMeasure P N))
    (cltK N ℓ ^ (2 * P.val.2 - 1) * ∫ v in (0 : ℝ)..ℓ.val⁻¹,
      deriv (loopMasterProfile ℓ ψh hψh).val v ^ 2)
  rw [abs_of_nonneg hD, abs_of_nonneg hB, abs_mul,
    abs_of_nonneg hC, abs_of_nonneg hJ'] at hb
  linarith only [hb, auxiliary_remainder_variance P N ℓ hρ ξ ψh hψh htr hPL]

end Riesz1.Internal

end
