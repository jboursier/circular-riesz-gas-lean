/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.CLT.Identity
public import Riesz1.Variance.AuxiliaryMixedCovariance
public import Riesz1.ToMathlib.LipschitzExpectationL2
public import Riesz1.Frozen.NormalizedStatistic
public import Riesz1.Frozen.PeriodizedProfileL2

/-!
# Statistics in the smoothing comparison

The Lipschitz assertion of the smoothing step in the proof of Theorem 3 needs no
quantitative variance result. The random variables are
`normalizedStatistic` and `cltStat` with its actual smoothing.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace Riesz1
namespace Internal

lemma smoothing_real_memLp (v : Profile) : MemLp v.val 2 volume := by
  have hv := v.property.re
  change MemLp (fun x => (v.val x : ℂ).re) 2 volume at hv
  simpa only [Complex.ofReal_re] using hv

lemma smoothing_cltStat_eq (P : Parameters) (p : Profile) (N : ℕ+) (a : Scale)
    {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {h : ℝ} (hh : 0 < h) :
    cltStat P N a (cltScaledFun hρ a hh
      ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩) =
      fun X : Configuration N => ((N : ℝ) * a.val) ^ (-P.val.2 / 2) *
        fluctuation ⟨cltScaledLift hρ a hh
          ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩,
          (smoothing_real_memLp ⟨_, cltScaledLift_memLp hρ a hh _⟩).integrable one_le_two⟩ X := by
  funext X
  have hcont : Continuous (cltScaledFun hρ a hh
      ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩) :=
    (cltRegCircle_contDiff hρ (observationLength a) hh
      ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩).continuous.comp
        (continuous_id.div_const a.val)
  have he := fluctuation_eq_fluctIntegral hcont (cltScaledFun_periodic hρ a hh
    ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩) X
  unfold cltStat cltK
  rw [← he]
  simp only [neg_div, cltScaledLift]

lemma smoothing_statistics_memLp (P : Parameters) (p : Profile) (ell : Scales)
    (N : ℕ+) {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) :
    MemLp (normalizedStatistic P p ell N) 2 (gibbsMeasure P N) ∧
      MemLp (cltStat P N (ell N) (cltScaledFun hρ (ell N) (cltDelta_pos P N (ell N))
        ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩))
        2 (gibbsMeasure P N) := by
  constructor
  · exact (memLp_fluctuation P N (smoothing_real_memLp
      ⟨testAtScale p (ell N), testAtScaleL2 p (ell N)⟩)).const_mul _
  · rw [smoothing_cltStat_eq]
    exact (memLp_fluctuation P N (smoothing_real_memLp
      ⟨_, cltScaledLift_memLp hρ (ell N) (cltDelta_pos P N (ell N)) _⟩)).const_mul _

end Internal

/-- The Lipschitz comparison in the smoothing step of the proof of Theorem 3, for every particle
number and every scale, including `N = 2`, without admissibility or a
quantitative variance hypothesis. -/
theorem clt_smoothing_lipschitz (P : Parameters) (p : Profile) (ell : Scales)
    (N : ℕ+) {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) (f : ℝ → ℝ)
    (hf : LipschitzWith 1 f)
    (hF : Integrable (fun X => f (normalizedStatistic P p ell N X)) (gibbsMeasure P N))
    (hG : Integrable (fun X => f (cltStat P N (ell N)
      (cltScaledFun hρ (ell N) (cltDelta_pos P N (ell N))
        ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩) X))
      (gibbsMeasure P N)) :
    let G := cltStat P N (ell N) (cltScaledFun hρ (ell N) (cltDelta_pos P N (ell N))
      ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩)
    |(∫ X, f (normalizedStatistic P p ell N X) ∂gibbsMeasure P N) -
      ∫ X, f (G X) ∂gibbsMeasure P N| ≤
        (eLpNorm (fun X => normalizedStatistic P p ell N X - G X) 2 (gibbsMeasure P N)).toReal := by
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  obtain ⟨hFm, hGm⟩ := Internal.smoothing_statistics_memLp P p ell N hρ
  exact abs_integral_comp_sub_le_eLpNorm_two (hFm.sub hGm) hf hF hG

end Riesz1
