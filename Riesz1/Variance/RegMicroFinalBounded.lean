/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroFinalStatistics
public import Riesz1.Variance.RegMicroFarRatesPowers

/-!
# Second moments for the bounded particle-number regime

An unconditional `L²` estimate for the original regularization error
in Lemma 5.3. In particular, bounded macroscopic
particle number, including `N=1`, does not require the small-radius
kernel argument. Compact profiles at bounded `K` require a local
second-moment estimate instead of this global `N²` estimate.
-/

public section

open MeasureTheory Filter

namespace Riesz1.Internal

/-- Circle regularization has uniformly bounded `L²` error, on the
existing pullback, for every positive radius. -/
theorem regMicro_integral_error_sq_le {ρ : ℝ → ℝ} (hρ : IsMollifier ρ)
    (L : Length)
    (f : {f : Circle L → ℝ // MemLp (fun z => (f z : ℂ)) 2 (arclength L)})
    (h : ℝ) (hh : 0 < h) :
    (∫ z : UnitAddCircle, (loopMasterPullback L f.val z-
      loopMasterPullback L (cltRegCircle hρ L hh f) z)^2) ≤
        4*∫ z : UnitAddCircle, (loopMasterPullback L f.val z)^2 := by
  have hf := loopMasterPullback_memLp L f
  have hs := hasSum_norm_sq_circleCoeff (loopMasterPullback L f.val) hf
  have heq : (∫ z : UnitAddCircle, (loopMasterPullback L f.val z-
      loopMasterPullback L (cltRegCircle hρ L hh f) z)^2) =
      ∑' k : ℤ, ‖circleCoeff (loopMasterPullback L f.val) k‖^2 *
        (mollifierFT ρ (h*k/L.val)-1)^2 := by
    rw [← integral_sq_pullback_regularize_sub hρ L f hh]
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by ring
  have hb (k : ℤ) : ‖circleCoeff (loopMasterPullback L f.val) k‖^2 *
      (mollifierFT ρ (h*k/L.val)-1)^2 ≤
        4*‖circleCoeff (loopMasterPullback L f.val) k‖^2 := by
    have hm := abs_le.mp (mollifierFT_abs_le_one hρ.isCircleMollifier (h*k/L.val))
    have hp : (mollifierFT ρ (h*k/L.val)-1)^2 ≤ 4 := by nlinarith [sq_nonneg (mollifierFT ρ (h*k/L.val))]
    nlinarith [sq_nonneg ‖circleCoeff (loopMasterPullback L f.val) k‖]
  have hs' : Summable (fun k : ℤ => ‖circleCoeff (loopMasterPullback L f.val) k‖^2 *
      (mollifierFT ρ (h*k/L.val)-1)^2) :=
    Summable.of_nonneg_of_le (fun k => by positivity) hb (hs.summable.mul_left 4)
  rw [heq]
  calc
    _ ≤ ∑' k : ℤ, 4*‖circleCoeff (loopMasterPullback L f.val) k‖^2 :=
      hs'.tsum_le_tsum hb (hs.summable.mul_left 4)
    _ = _ := by rw [tsum_mul_left, hs.tsum_eq]; simp only [← pow_two]

/-- The original mixed error has a finite second moment and its
variance is at most `16 N²` times the original pulled-back square mass.
No admissibility or small-radius assumption is needed. -/
theorem regMicro_error_variance_l2 (P : Parameters) (N : ℕ+) (ℓ : Scale)
    {ρ : ℝ → ℝ} (hρ : IsMollifier ρ)
    (f : {f : Circle (loopMasterLength ℓ) → ℝ //
      MemLp (fun z => (f z : ℂ)) 2 (arclength (loopMasterLength ℓ))}) :
    ∃ hE : MemLp (mixedStat P N ℓ (subCircleL2 f (mixedReg hρ N ℓ f))) 2 (gibbsMeasure P N),
      variance (gibbsMeasure P N) _ (hE.integrable one_le_two) ≤
        ENNReal.ofReal (16*(N : ℝ)^2 * ∫ z : UnitAddCircle,
          (loopMasterPullback (loopMasterLength ℓ) f.val z)^2) := by
  let E := subCircleL2 f (mixedReg hρ N ℓ f)
  let g := loopMasterPullback (loopMasterLength ℓ) E.val
  have hg := memLp_real_of_complex (loopMasterPullback_memLp _ E)
  have hF := memLp_fluctuation P N hg
  have : IsProbabilityMeasure (gibbsMeasure P N) := (modelWellDefined P N).2.2
  refine ⟨hF, ?_⟩
  have hV : variance (gibbsMeasure P N) (mixedStat P N ℓ E) (hF.integrable one_le_two) ≤
      ENNReal.ofReal (4*(N : ℝ)^2*∫ z, g z^2) := by
    apply (variance_eq_ofReal_integral_sq (gibbsMeasure P N) (mixedStat P N ℓ E) hF).trans_le
    have hm : (∫ X, mixedStat P N ℓ E X ∂gibbsMeasure P N) = 0 :=
      integral_fluctuation_eq_zero P N hg
    rw [hm]
    simp only [sub_zero]
    exact ENNReal.ofReal_le_ofReal (integral_sq_fluctuation_le P N hg)
  apply hV.trans (ENNReal.ofReal_le_ofReal ?_)
  have he := regMicro_integral_error_sq_le hρ (loopMasterLength ℓ) f
    (cltK N ℓ)⁻¹ (inv_pos.mpr (cltK_pos N ℓ))
  have he' : (∫ z : UnitAddCircle, g z^2) ≤
      4*∫ z : UnitAddCircle, (loopMasterPullback (loopMasterLength ℓ) f.val z)^2 := by
    simpa only [g, E, loopMasterPullback_subCircleL2, mixedReg, loopMasterLengthTest,
      mixedRegCircle] using he
  nlinarith [mul_le_mul_of_nonneg_left he' (by positivity : 0 ≤ 4*(N : ℝ)^2)]

end Riesz1.Internal
