/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroFinalStatistics
public import Riesz1.Variance.MicroLocalUnit
public import Riesz1.ToMathlib.SizeBiasedVariance

/-!
# Local variance for almost everywhere supported tests

The local second-moment step of Lemma 5.3, on the
actual `L²` carrier. Support is only required almost everywhere, as is
necessary for singular profiles and their regularization errors.
-/

public section

open MeasureTheory Set Filter

namespace Riesz1.Internal

/-- Local square mass controls a statistic even when its representative
has exceptional values outside its essential support. The constant
precedes the particle number, center, radius and test. -/
theorem regMicro_local_variance_ae (P : Parameters) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (N : ℕ+)
      (c : UnitAddCircle) (r : ℝ), 2*(N : ℝ)*r ≤ R →
      ∀ (f : UnitAddCircle → ℝ) (hf : MemLp f 2 volume),
        (∀ᵐ z, r < dist z c → f z = 0) →
        variance (gibbsMeasure P N) (linearStatistic f)
          ((memLp_linearStatistic P N hf).integrable one_le_two) ≤
            ENNReal.ofReal (C*(N : ℝ)*∫ z, f z^2) := by
  obtain ⟨C, hC, hlocal⟩ := micro_local_unit P R
  refine ⟨C, hC, fun hPL N c r hr f hf hsupp => ?_⟩
  let I := Metric.closedBall c r
  let g := I.indicator (hf.aestronglyMeasurable.mk f)
  have hg : Measurable g := hf.aestronglyMeasurable.measurable_mk.indicator
    Metric.isClosed_closedBall.measurableSet
  have hfg : f =ᵐ[volume] g := by
    filter_upwards [hf.aestronglyMeasurable.ae_eq_mk, hsupp] with z hz hs
    by_cases hzi : z ∈ I
    · simpa only [g, indicator_of_mem hzi] using hz
    · rw [show g z = 0 from indicator_of_notMem hzi _]
      exact hs (lt_of_not_ge hzi)
  have hgLp : MemLp g 2 volume := hf.ae_eq hfg
  have hdiam : ∀ u ∈ I, ∀ v ∈ I, dist u v ≤ R/(N : ℝ) := by
    intro u hu v hv
    have hN : 0 < (N : ℝ) := by positivity
    apply (le_div_iff₀ hN).mpr
    have ht := dist_triangle u c v
    rw [dist_comm c v] at ht
    nlinarith [show dist u c ≤ r from hu, show dist v c ≤ r from hv]
  have hbound := hlocal hPL N I hdiam g hg (fun z hz => indicator_of_notMem hz _)
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  have hv := variance_le_lintegral_sq_sub (gibbsMeasure P N)
    (memLp_linearStatistic P N hgLp) 0
  have hv' : variance (gibbsMeasure P N) (linearStatistic g)
      ((memLp_linearStatistic P N hgLp).integrable one_le_two) ≤
      ENNReal.ofReal (C*(N : ℝ)*∫ z, g z^2) := by
    apply hv.trans
    calc
      _ ≤ ∫⁻ X : Configuration N, ENNReal.ofReal
          ((∑ i : Fin (N : ℕ), |g (X.val i)|)^2) ∂gibbsMeasure P N := by
        apply lintegral_mono
        intro X
        apply ENNReal.ofReal_le_ofReal
        simp only [sub_zero, linearStatistic]
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _)
          (Finset.abs_sum_le_sum_abs (s := Finset.univ) (f := fun i => g (X.val i))) 2
      _ ≤ _ := hbound
      _ = _ := by
        rw [← ofReal_integral_eq_lintegral_ofReal hgLp.integrable_sq
          (Eventually.of_forall fun z => sq_nonneg (g z)),
          ← ENNReal.ofReal_mul hC.le,
          ← ENNReal.ofReal_mul (mul_nonneg hC.le (by positivity))]
  have heq := auxiliary_variance_congr
    ((memLp_linearStatistic P N hf).integrable one_le_two)
    ((memLp_linearStatistic P N hgLp).integrable one_le_two)
    (linearStatistic_ae_eq P N hfg)
  rw [heq]
  rwa [← integral_congr_ae (hfg.mono fun z hz => congrArg (fun t : ℝ => t^2) hz)] at hv'

/-- The local variance estimate on an observation circle, for any actual
`L²` test with bounded physical support and `K≤K₀`. The bound retains
the exact pulled-back square mass. -/
theorem regMicro_mixed_local_variance_ae (P : Parameters) (R K₀ : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (_hPL : External.PrekopaLeindler) (N : ℕ+) (a : Scale),
      cltK N a ≤ K₀ →
      ∀ (f : {f : Circle (loopMasterLength a) → ℝ //
        MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength a))}),
        (∀ᵐ z ∂arclength (loopMasterLength a), R < dist z 0 → f.val z = 0) →
        ∃ hF : MemLp (mixedStat P N a f) 2 (gibbsMeasure P N),
          variance (gibbsMeasure P N) _ (hF.integrable one_le_two) ≤
            ENNReal.ofReal (C*(N : ℝ)*∫ z : UnitAddCircle,
              (loopMasterPullback (loopMasterLength a) f.val z)^2) := by
  obtain ⟨C, hC, hlocal⟩ := regMicro_local_variance_ae P (2*K₀*R)
  refine ⟨C, hC, fun hPL N a hK f hs => ?_⟩
  let L := loopMasterLength a
  have : Fact (0 < L.val) := ⟨L.property⟩
  let g := loopMasterPullback L f.val
  have hg : MemLp g 2 volume := (loopMasterPullback_memLp L f).re
  have hmap : ∀ᵐ z ∂(volume : Measure UnitAddCircle).map
      (AddCircle.equivAddCircle 1 L.val one_ne_zero L.property.ne'),
      R < dist z 0 → f.val z = 0 := by
    rw [map_circleScale_volume]
    exact Measure.ae_smul_measure hs _
  have hsg : ∀ᵐ z : UnitAddCircle, a.val*R < dist z 0 → g z = 0 := by
    filter_upwards [ae_of_ae_map
      (AddCircle.continuous_equivAddCircle ..).measurable.aemeasurable hmap] with z hz hd
    apply hz
    have hd' := circleScale_dist L.val z 0
    simp only [map_zero] at hd'
    rw [hd']
    have hm := mul_lt_mul_of_pos_left hd (inv_pos.mpr a.property.1)
    rw [← mul_assoc, inv_mul_cancel₀ a.property.1.ne', one_mul] at hm
    exact hm
  have hrad : 2*(N : ℝ)*(a.val*R) ≤ 2*K₀*R := by
    have hm := mul_le_mul_of_nonneg_right hK hR
    change ((N : ℝ)*a.val)*R ≤ K₀*R at hm
    nlinarith only [hm]
  have hv := hlocal hPL N 0 (a.val*R) hrad g hg hsg
  have hF : MemLp (mixedStat P N a f) 2 (gibbsMeasure P N) := memLp_fluctuation P N hg
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  have hshift : variance (gibbsMeasure P N) (mixedStat P N a f) (hF.integrable one_le_two) =
      variance (gibbsMeasure P N) (linearStatistic g)
        ((memLp_linearStatistic P N hg).integrable one_le_two) :=
    frozenVariance_sub_const ((memLp_linearStatistic P N hg).integrable one_le_two)
      ((N : ℝ)*∫ z, g z)
  exact ⟨hF, hshift.trans_le hv⟩

end Riesz1.Internal
