/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.ErrorTwoRates
public import Riesz1.CLT.Identity
public import Riesz1.Variance.VarAlPiecesLoopMemLp
public import Riesz1.ToMathlib.BoundedCovarianceVariance
public import Riesz1.Bridges.FluctuationSquare
import all Riesz1.Variance.LoopIBPMoments
import all Riesz1.Variance.LoopIBPUniform
import all Riesz1.Variance.LoopScale

/-!
# From the two variance bounds to the second Stein error

The last paragraph of the proof of the second error bound in Theorem 3.
Integrability is proved on the loop, fluctuation and remainder objects.
The internal assembly lemma assumes the displayed joint variance bound.
It does not claim that the two variance estimates have been proved.
-/

public section

open MeasureTheory
open scoped ContDiff ENNReal

namespace Riesz1

/-- A continuous periodic test has square-integrable fluctuations. -/
theorem errorTwo_memLp_fluctIntegral (P : Parameters) (N : ℕ+) {f : ℝ → ℝ}
    (hf : Continuous f) (hp : Function.Periodic f 1) :
    MemLp (fun X : Configuration N => fluctIntegral f N X.val) 2 (gibbsMeasure P N) := by
  have hm := memLp_lift_of_continuous hf hp
  have he : (fun X : Configuration N => fluctIntegral f N X.val) =
      fluctuation ⟨hp.lift, hm.integrable one_le_two⟩ := by
    funext X
    exact (fluctuation_eq_fluctIntegral hf hp X).symm
  rw [he]
  exact memLp_fluctuation P N hm

/-- The two components of `B_N` are square integrable, including `N = 1`. -/
theorem errorTwo_components_memLp (hPL : External.PrekopaLeindler)
    (P : Parameters) (N : ℕ+) (a : Scale) (ψ : LoopScaleProfile a.val)
    (hψ : ContDiff ℝ ∞ ψ.val) :
    MemLp (loopOnConfiguration (parametersExponent P) N a ψ) 2 (gibbsMeasure P N) ∧
      MemLp (fun X : Configuration N =>
        fluctIntegral (fun u => deriv ψ.val (u / a.val)) N X.val) 2 (gibbsMeasure P N) := by
  obtain ⟨M, hM⟩ := loopScaleField_lipschitz ψ
  refine ⟨memLp_loopFunctional_gibbs P hPL N P.property.2.1 P.property.2.2 hM
    (loopScaleField_periodic ψ.property.1), ?_⟩
  have hd : ContDiff ℝ ∞ (deriv ψ.val) := by simpa using hψ.deriv'
  apply errorTwo_memLp_fluctIntegral P N (hd.continuous.comp (continuous_id.div_const _))
  intro u
  change deriv ψ.val ((u + 1) / a.val) = deriv ψ.val (u / a.val)
  rw [add_div, one_div, (Riesz1.periodic_deriv ψ.property.1)]

/-- The remainder `cltRemainder` has finite second moment. -/
theorem cltRemainder_memLp (hPL : External.PrekopaLeindler)
    (P : Parameters) (N : ℕ+) (a : Scale) (ψ : LoopScaleProfile a.val)
    (hψ : ContDiff ℝ ∞ ψ.val) :
    MemLp (cltRemainder P N a ψ) 2 (gibbsMeasure P N) := by
  obtain ⟨hL, hD⟩ := errorTwo_components_memLp hPL P N a ψ hψ
  exact (hL.const_mul P.val.1).sub hD

namespace Internal

/-- Last implication of the second error bound in the proof of Theorem 3, for every measurable
statistic `G` and every bounded continuous `u`. The estimate is uniform in both.
The hypothesis is the displayed joint variance estimate, on exactly these
objects. This internal lemma is not the statement of the paper. -/
theorem clt_error2_of_variance_bound (hPL : External.PrekopaLeindler)
    (P : Parameters) (N : ℕ+) (a : Scale) (hK : 1 ≤ (N : ℝ) * a.val)
    (ψ : LoopScaleProfile a.val) (hψ : ContDiff ℝ ∞ ψ.val)
    (C τ α : ℝ) (hC : 0 ≤ C)
    (hV : ∃ hL : Integrable (loopOnConfiguration (parametersExponent P) N a ψ) (gibbsMeasure P N),
      ∃ hD : Integrable (fun X : Configuration N =>
        fluctIntegral (fun u => deriv ψ.val (u / a.val)) N X.val) (gibbsMeasure P N),
        variance (gibbsMeasure P N) _ hL + variance (gibbsMeasure P N) _ hD ≤
          ENNReal.ofReal (C * (((N : ℝ) * a.val) ^ (2 * τ) *
            ((N : ℝ) * a.val + ((N : ℝ) * a.val) ^ (2 * (1 - P.val.2 + α))))))
    {G : Configuration N → ℝ} (hG : AEStronglyMeasurable G (gibbsMeasure P N))
    {u : ℝ → ℝ} (hu : Continuous u) {M : ℝ} (hM : 0 ≤ M) (hub : ∀ y, |u y| ≤ M) :
    |(-(cltK N a ^ (-1 + P.val.2 / 2))) *
      gibbsCov (gibbsMeasure P N) (fun X => u (G X)) (cltRemainder P N a ψ)| ≤
        (2 * Real.sqrt (2 * (P.val.1 ^ 2 + 1) * C)) * M *
          ((N : ℝ) * a.val) ^ (max ((P.val.2 - 1) / 2) (α - P.val.2 / 2) + τ) := by
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  obtain ⟨hL, hD⟩ := errorTwo_components_memLp hPL P N a ψ hψ
  have hB := cltRemainder_memLp hPL P N a ψ hψ
  obtain ⟨hiL, hiD, hV⟩ := hV
  let K : ℝ := (N : ℝ) * a.val
  let R : ℝ := K ^ (2 * τ) * (K + K ^ (2 * (1 - P.val.2 + α)))
  let A : ℝ := 2 * (P.val.1 ^ 2 + 1)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hR : 0 ≤ R := by dsimp [R, K]; positivity
  have hcoL : ENNReal.ofReal (2 * P.val.1 ^ 2) ≤ ENNReal.ofReal A :=
    ENNReal.ofReal_le_ofReal (by dsimp [A]; linarith)
  have hcoD : (2 : ℝ≥0∞) ≤ ENNReal.ofReal A := by
    rw [← ENNReal.ofReal_ofNat]
    exact ENNReal.ofReal_le_ofReal (by dsimp [A]; nlinarith [sq_nonneg P.val.1])
  have hBV : variance (gibbsMeasure P N) (cltRemainder P N a ψ)
      (hB.integrable one_le_two) ≤ ENNReal.ofReal ((A * C) * R) := by
    calc
      _ ≤ ENNReal.ofReal (2 * P.val.1 ^ 2) * variance (gibbsMeasure P N) _ hiL +
          2 * variance (gibbsMeasure P N) _ hiD :=
        variance_const_mul_sub_le_two hL hD P.val.1
      _ ≤ ENNReal.ofReal A * (variance (gibbsMeasure P N) _ hiL +
          variance (gibbsMeasure P N) _ hiD) := by
        rw [mul_add]
        exact add_le_add (mul_le_mul_left hcoL _) (mul_le_mul_left hcoD _)
      _ ≤ ENNReal.ofReal A * ENNReal.ofReal (C * R) := mul_le_mul_right hV _
      _ = _ := by rw [← ENNReal.ofReal_mul hA]; congr 1; ring
  have hBreal : (variance (gibbsMeasure P N) (cltRemainder P N a ψ)
      (hB.integrable one_le_two)).toReal ≤ (A * C) * R := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hBV
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  have hcov := (abs_covariance_le_bound_sqrt_variance
    (hu.comp_aestronglyMeasurable hG) hB hM (ae_of_all _ fun X => hub (G X))).2
  change |gibbsCov (gibbsMeasure P N) (fun X => u (G X)) (cltRemainder P N a ψ)| ≤ _ at hcov
  have hsqrt : Real.sqrt (variance (gibbsMeasure P N) (cltRemainder P N a ψ)
      (hB.integrable one_le_two)).toReal ≤ Real.sqrt (A * C) * Real.sqrt R := by
    simpa only [Real.sqrt_mul (mul_nonneg hA hC)] using Real.sqrt_le_sqrt hBreal
  rw [abs_mul, abs_neg, abs_of_nonneg (Real.rpow_nonneg (cltK_pos N a).le _)]
  calc
    _ ≤ K ^ (-1 + P.val.2 / 2) * (M * (Real.sqrt (A * C) * Real.sqrt R)) :=
      mul_le_mul_of_nonneg_left (hcov.trans (mul_le_mul_of_nonneg_left hsqrt hM)) (by positivity)
    _ = (M * Real.sqrt (A * C)) * (K ^ (-1 + P.val.2 / 2) * Real.sqrt R) := by ring
    _ ≤ (M * Real.sqrt (A * C)) *
        (2 * K ^ (max ((P.val.2 - 1) / 2) (α - P.val.2 / 2) + τ)) :=
      mul_le_mul_of_nonneg_left (errorTwo_scaled_sqrt hK P.val.2 α τ) (by positivity)
    _ = _ := by dsimp only [A, K]; ring

end Internal
end Riesz1
