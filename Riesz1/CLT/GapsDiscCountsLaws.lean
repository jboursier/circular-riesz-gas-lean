/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.GapsDiscCountsNormal
public import Riesz1.Gibbs.UniformMarginals
public import Riesz1.Frozen.NormalLaw
public import Riesz1.Frozen.ParticleNumber
public import Riesz1.Frozen.ModelWellDefined
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Laws of the normalized counts

The laws of the normalized count and of the CLT normalized statistic of the arc profile, as
`ProbabilityMeasure ℝ`. The normalized count is the CLT statistic multiplied by the constant
`arcKappa`, so its law is the image of the CLT law under `x ↦ arcKappa * x`
(`map_normalizedCount_eq`). The Gaussian limit of variance `σ²` is carried to the Gaussian of
variance `κ²σ²` by the same map (`normalLaw_map_mul_real`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace Riesz1

/-- The arc counts are measurable functions of the configuration. -/
lemma measurable_arcCount {N : ℕ+} (c : UnitAddCircle) (a : ℝ) :
    Measurable (fun X : Configuration N => arcCount c a X) := by
  unfold arcCount
  refine Finset.measurable_sum _ fun i _ => ?_
  exact (measurable_arcIndicator c a).comp (measurable_coord N i)

/-- The normalized count is measurable. -/
lemma measurable_normalizedCount {N : ℕ+} (P : Parameters) (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2)
    (ell : Scales) :
    Measurable (fun X : Configuration N => normalizedCount P a ha ha1 ell N X) := by
  have hfun : (fun X : Configuration N => normalizedCount P a ha ha1 ell N X) =
      fun X => (arcCount 0 (a * (ell N).val) X - (N : ℝ) * (2 * (a * (ell N).val))) /
        Real.sqrt ((N : ℝ) ^ P.val.2 *
          periodicZeta (parametersExponent P) ((2 * a * (ell N).val : ℝ) : UnitAddCircle)) :=
    funext fun X => normalizedCount_eq_arcCount P ha ha1 ell N X
  rw [hfun]
  exact (((measurable_arcCount 0 _).sub measurable_const).div_const _)

/-- The CLT normalized statistic of the arc profile is measurable. -/
lemma measurable_normalizedStatistic_arcProfile {N : ℕ+} (P : Parameters) {a : ℝ} (ha0 : 0 < a)
    (ha1 : a < 1 / 2) (ell : Scales) :
    Measurable (fun X : Configuration N => normalizedStatistic P (arcProfile a) ell N X) := by
  have hfun : (fun X : Configuration N => normalizedStatistic P (arcProfile a) ell N X) =
      fun X => ((N : ℝ) * (ell N).val) ^ (-P.val.2 / 2) *
        (arcCount 0 (a * (ell N).val) X - (N : ℝ) * (2 * (a * (ell N).val))) :=
    funext fun X => normalizedStatistic_arcProfile P ha0 ha1 ell N X
  rw [hfun]
  exact measurable_const.mul ((measurable_arcCount 0 _).sub measurable_const)

/-- The constant `κ(ℓ) = sqrt(v_s) / sqrt(σ²(ℓ))` relating the normalized count to the CLT
statistic at scale `ℓ`. -/
def arcKappa (P : Parameters) (a : ℝ) (_ha0 : 0 < a) (_ha1 : a < 1 / 2) (ell : Scale) : ℝ :=
  Real.sqrt (countVariance P) / Real.sqrt (circleVariance P (arcProfile a) ell).toReal

/-- The normalized count is `κ` times the CLT normalized statistic. -/
lemma normalizedCount_eq_arcKappa_mul (P : Parameters) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1 / 2)
    (ell : Scales) (N : ℕ+) (X : Configuration N) :
    normalizedCount P a ha0 ha1 ell N X =
      arcKappa P a ha0 ha1 (ell N) * normalizedStatistic P (arcProfile a) ell N X := by
  have hℓ : 0 < (ell N).val := (ell N).property.1
  have hℓ1 : (ell N).val ≤ 1 := (ell N).property.2
  have h0 : 0 < 2 * a * (ell N).val := by positivity
  have h1 : 2 * a * (ell N).val < 1 := by nlinarith
  have hV : 0 < periodicZeta (parametersExponent P)
      ((2 * a * (ell N).val : ℝ) : UnitAddCircle) := periodicZeta_pos _ h0 h1
  have hv : 0 < countVariance P := gapsDisc_countVariance_pos P
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  rw [normalizedCount_eq_arcCount, normalizedStatistic_arcProfile P ha0 ha1 ell N X, arcKappa,
    circleVariance_arcProfile ha0 ha1 P (ell N)]
  have key := inv_sqrt_eq_normalization (P.val.2) (N : ℝ) (ell N).val (countVariance P)
    (periodicZeta (parametersExponent P) ((2 * a * (ell N).val : ℝ) : UnitAddCircle))
    hNpos hℓ hv hV
  rw [div_eq_mul_one_div, key]
  ring

/-- The image of `N(0, σ²)` under `x ↦ κ x` is `N(0, κ² σ²)`, with the variances given as real
numbers `σ, v ≥ 0` through `Real.toNNReal`. -/
lemma normalLaw_map_mul_real (κ σ v : ℝ) (hσ : 0 ≤ σ) (hv : 0 ≤ v) (h : κ ^ 2 * σ = v) :
    (normalLaw (Real.toNNReal σ)).map (κ * ·) = normalLaw (Real.toNNReal v) := by
  unfold normalLaw
  rw [ProbabilityTheory.gaussianReal_map_const_mul, mul_zero]
  congr 1
  apply NNReal.eq
  rw [NNReal.coe_mul, NNReal.coe_mk, Real.coe_toNNReal _ hσ, Real.coe_toNNReal _ hv]
  exact h

/-- The Gibbs law as a probability measure. -/
def gibbsProb (P : Parameters) (N : ℕ+) : ProbabilityMeasure (Configuration N) :=
  ⟨gibbsMeasure P N, (modelWellDefined P N).2.2⟩

/-- The law of the normalized count under the Gibbs law. -/
def countLaw (P : Parameters) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1 / 2) (ell : Scales) (N : ℕ+) :
    ProbabilityMeasure ℝ :=
  (gibbsProb P N).map (normalizedCount P a ha0 ha1 ell N)

/-- The law of the CLT normalized statistic of the arc profile under the Gibbs law. -/
def statLaw (P : Parameters) {a : ℝ} (_ha0 : 0 < a) (_ha1 : a < 1 / 2) (ell : Scales) (N : ℕ+) :
    ProbabilityMeasure ℝ :=
  (gibbsProb P N).map (normalizedStatistic P (arcProfile a) ell N)

/-- The law of the normalized count is the law of the CLT statistic pushed forward by `κ`. -/
lemma countLaw_eq_map_statLaw (P : Parameters) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1 / 2)
    (ell : Scales) (N : ℕ+) :
    countLaw P ha0 ha1 ell N =
      (statLaw P ha0 ha1 ell N).map (arcKappa P a ha0 ha1 (ell N) * ·) := by
  apply Subtype.ext
  unfold countLaw statLaw
  change (gibbsMeasure P N).map (normalizedCount P a ha0 ha1 ell N) =
    ((gibbsMeasure P N).map (normalizedStatistic P (arcProfile a) ell N)).map
      (arcKappa P a ha0 ha1 (ell N) * ·)
  rw [Measure.map_map (measurable_const_mul _)
    (measurable_normalizedStatistic_arcProfile P ha0 ha1 ell)]
  congr 1
  funext X
  exact normalizedCount_eq_arcKappa_mul P ha0 ha1 ell N X

end Riesz1

end
end
