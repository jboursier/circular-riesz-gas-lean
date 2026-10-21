/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroUniformSupport

/-!
# Support and square-mass contraction under circle smoothing

Analytic steps for the two convolution families in Lemma 5.3.
They concern the existing circle smoothing operator,
at every positive radius, and require no separation of marked points.
-/

public section

open MeasureTheory Set Filter

namespace Riesz1.Internal

/-- Smoothing expands essential circle support by at most half its
radius. The conclusion is pointwise for the smooth representative. -/
theorem regMicro_smoothing_support (L : Length)
    (f : {f : Circle L → ℝ // MemLp (fun z => (f z : ℂ)) 2 (arclength L)})
    {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {h : ℝ} (hh : 0 < h) (R : ℝ)
    (hs : ∀ᵐ z ∂arclength L, R < dist z 0 → f.val z = 0) :
    ∀ z : Circle L, R+h/2 < dist z 0 → cltRegCircle hρ L hh f z = 0 := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  rintro z hz
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  rw [cltRegCircle_coe]
  unfold circleMollify
  rw [intervalIntegral.integral_of_le (by linarith [L.property])]
  have hmp := AddCircle.measurePreserving_mk L.val (-(L.val/2))
  have hs' := hmp.quasiMeasurePreserving.ae hs
  rw [show -(L.val/2)+L.val = L.val/2 by ring] at hs'
  apply integral_eq_zero_of_ae
  filter_upwards [hs'] with y hy
  change f.val (y : Circle L)*periodMollifier ρ L.val h (x-y) = 0
  by_cases hyr : R < dist (y : Circle L) 0
  · rw [hy hyr, zero_mul]
  · have hd : h/2 ≤ dist (x : Circle L) (y : Circle L) := by
      have ht := dist_triangle (x : Circle L) (y : Circle L) 0
      linarith [le_of_not_gt hyr]
    have hk : periodMollifier ρ L.val h (x-y) = 0 := by
      unfold periodMollifier
      suffices hn : ∀ n : ℤ, scaledMollifier ρ h (x-y+n*L.val) = 0 by
        simp only [hn, tsum_zero]
      intro n
      apply scaledMollifier_eq_zero hρ hh
      rw [dist_coe_eq_circDist_sub L.property] at hd
      have hn := circDist_le_abs_sub L.property (x-y) (-n)
      have he : x-y-L.val*((-n : ℤ) : ℝ) = x-y+n*L.val := by push_cast; ring
      rw [he] at hn
      exact hd.trans hn
    rw [hk, mul_zero]

/-- Positive normalized circle smoothing contracts square mass,
including at radii larger than the circle circumference. -/
theorem regMicro_smoothing_sq_le (L : Length)
    (f : {f : Circle L → ℝ // MemLp (fun z => (f z : ℂ)) 2 (arclength L)})
    {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {h : ℝ} (hh : 0 < h) :
    (∫ z : UnitAddCircle, (loopMasterPullback L (cltRegCircle hρ L hh f) z)^2) ≤
      ∫ z : UnitAddCircle, (loopMasterPullback L f.val z)^2 := by
  let g := loopMasterLengthTest L (cltRegCircle hρ L hh f) (cltRegCircle_contDiff hρ L hh f)
  have hs := hasSum_norm_sq_circleCoeff (loopMasterPullback L f.val) (loopMasterPullback_memLp L f)
  have ht := hasSum_norm_sq_circleCoeff (loopMasterPullback L g.val) (loopMasterPullback_memLp L g)
  have hb (k : ℤ) : ‖circleCoeff (loopMasterPullback L g.val) k‖^2 ≤
      ‖circleCoeff (loopMasterPullback L f.val) k‖^2 := by
    change ‖circleCoeff (loopMasterPullback L (cltRegCircle hρ L hh f)) k‖^2 ≤ _
    rw [circleCoeff_pullback_cltRegCircle hρ L f hh k, norm_mul, Complex.norm_real]
    apply pow_le_pow_left₀ (by positivity)
    exact mul_le_of_le_one_right (norm_nonneg _)
      (by simpa only [Real.norm_eq_abs] using mollifierFT_abs_le_one hρ.isCircleMollifier (h*k/L.val))
  have hv := ht.summable.tsum_le_tsum hb hs.summable
  rw [ht.tsum_eq, hs.tsum_eq] at hv
  simpa only [g, loopMasterLengthTest, ← pow_two] using hv

/-- The periodization always has essential support inside the
radius-one-half ball, including arbitrary endpoint representatives. -/
theorem regMicro_periodized_support_half (p : Profile) (a : Scale) :
    ∀ z : Circle (observationLength a), (1/2 : ℝ) < dist z 0 →
      periodizedProfile p (observationLength a) z = 0 := by
  intro z hz
  rw [admissibility_periodizedProfile_eq_zeroExtension p (observationLength a)
    ((one_le_inv₀ a.property.1).mpr a.property.2)]
  have hd := regMicro_abs_centralRep_eq_dist (observationLength a) z
  simp only [zeroExtension, not_lt.mpr (by linarith : (1/2 : ℝ) ≤
    |centralRep (observationLength a) z|), ite_false]

end Riesz1.Internal
