/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroFinalBounded
public import Riesz1.Variance.RegMicroFinalEnvelopes
public import Riesz1.Variance.APrioriFinalCircle
public import Riesz1.ToMathlib.CircleAEFromCell
public import Riesz1.Variance.RegMicroUniformMass

/-!
# Uniform support and square mass of the microscopic error

For bounded `K` the zero extension already gives a bounded
microscopic support. No profile regularity is needed for this step of
Lemma 5.3, and every positive smoothing radius at most
one is included.
-/

public section

open MeasureTheory Set Filter

namespace Riesz1.Internal

/-- On every enlarged circle, smoothing a periodized profile at a radius
at most one leaves its error essentially supported in the radius-one ball.
This remains valid when that ball fills the circle. -/
theorem regMicro_periodized_error_support (p : Profile) (a : Scale)
    {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    let L := observationLength a
    let f := (⟨periodizedProfile p L, periodizedProfileL2 p a⟩ :
      {f : Circle L → ℝ // MemLp (fun z => (f z : ℂ)) 2 (arclength L)})
    ∀ᵐ z ∂arclength L, 1 < dist z 0 → f.val z-cltRegCircle hρ L hh f z = 0 := by
  dsimp only
  let L := observationLength a
  let f := (⟨periodizedProfile p L, periodizedProfileL2 p a⟩ :
      {f : Circle L → ℝ // MemLp (fun z => (f z : ℂ)) 2 (arclength L)})
  let e := fun z => f.val z-cltRegCircle hρ L hh f z
  let I := Metric.closedBall (0 : Circle L) 1
  have hL : 1 ≤ L.val := (one_le_inv₀ a.property.1).mpr a.property.2
  have he : AEMeasurable e (arclength L) := by
    have hf : MemLp f.val 2 (arclength L) := f.property.re
    have hc : Continuous (cltRegCircle hρ L hh f) :=
      (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.2
        (cltRegCircle_contDiff hρ L hh f).continuous
    exact hf.aestronglyMeasurable.aemeasurable.sub hc.measurable.aemeasurable
  have hs : ∀ᵐ x : ℝ, (1/2 : ℝ) ≤ |x| → zeroExtension p x = 0 :=
    Eventually.of_forall fun x hx => by simp only [zeroExtension, not_lt.mpr hx, ite_false]
  have heq : e =ᵐ[arclength L] I.indicator e := by
    apply ae_circle_of_ae_cell he (he.indicator Metric.isClosed_closedBall.measurableSet)
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae (show ∀ᵐ x : ℝ, x ≠ L.val/2 by rw [ae_iff]; simp)] with x hx hxend
    by_cases hi : (x : Circle L) ∈ I
    · exact (indicator_of_mem hi e).symm
    · rw [indicator_of_notMem hi]
      have habs : |x| ≤ L.val/2 := abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
      have hdist : 1 < |x| := by
        have hrep := abs_centralRep_coe_of_mem_Icc L (u := x) ⟨hx.1.le, hx.2⟩
        rw [regMicro_abs_centralRep_eq_dist] at hrep
        exact hrep ▸ lt_of_not_ge hi
      dsimp only [e, f]
      rw [cltRegCircle_coe, regMicroKernel_periodized_coe_eq p L hL
        ⟨by linarith [hx.1], lt_of_le_of_ne hx.2 hxend⟩,
        regMicroKernel_mollify_eq_zero_of_support hρ p L hL hh hs habs
          (by linarith), sub_zero]
      simp only [zeroExtension, not_lt.mpr (by linarith : (1/2 : ℝ) ≤ |x|), ite_false]
  filter_upwards [heq] with z hz hd
  change e z = 0
  rw [hz]
  exact indicator_of_notMem (show z ∉ I from not_le.mpr hd) e

/-- The pulled-back microscopic error has square mass at most four
times the scale times the fixed line square mass. -/
theorem regMicro_periodized_error_sq_le (p : Profile) (a : Scale)
    {ρ : ℝ → ℝ} (hρ : IsMollifier ρ) {h : ℝ} (hh : 0 < h) :
    let L := observationLength a
    let f := (⟨periodizedProfile p L, periodizedProfileL2 p a⟩ :
      {f : Circle L → ℝ // MemLp (fun z => (f z : ℂ)) 2 (arclength L)})
    (∫ z : UnitAddCircle, (loopMasterPullback L f.val z-
      loopMasterPullback L (cltRegCircle hρ L hh f) z)^2) ≤
        4*a.val*∫ x : ℝ, (zeroExtension p x)^2 := by
  dsimp only
  have hb := regMicro_integral_error_sq_le hρ (observationLength a)
    ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ h hh
  rw [integral_sq_loopMasterPullback, integral_sq_periodizedProfile p (observationLength a)
    ((one_le_inv₀ a.property.1).mpr a.property.2)] at hb
  simpa only [observationLength, inv_inv, mul_assoc] using hb

end Riesz1.Internal
