/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.CirclePowerShortInterval
public import Riesz1.ToMathlib.CircleMollifyError
public import Riesz1.ToMathlib.LocallyIntegrablePuncturedDerivative

/-!
# Hölder increments through finitely many circle marks

For a continuous function, an integrable marked derivative envelope controls
increments even across the marks. The constant is uniform in the circle
length and mark positions. No assumption of absolute continuity is added.
-/

public section

open MeasureTheory Set Filter

namespace Riesz1

/-- Short increments through the marks from an integrable derivative bound. -/
theorem finiteMark_holder_of_deriv {L γ A : ℝ} [Fact (0 < L)]
    {ι : Type*} [Fintype ι] [Nonempty ι] (marks : ι → ℝ)
    {f : ℝ → ℝ} (hc : Continuous f) (hA : 0 ≤ A) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hderiv : ∀ x : ℝ, (∀ j, (x : AddCircle L) ≠ (marks j : AddCircle L)) →
      DifferentiableAt ℝ f x ∧ |deriv f x| ≤ A *
        cappedMarkDistance (fun j => (marks j : AddCircle L)) (x : AddCircle L) ^ (-γ))
    {x y : ℝ} (hshort : |y - x| ≤ L) (hsmall : |y - x| ≤ 1) :
    |f y - f x| ≤
      A * (1 + (Fintype.card ι : ℝ) * (1 + 2 / (1 - γ))) * |y - x| ^ (1 - γ) := by
  let S := {t : ℝ | ∃ j, (t : AddCircle L) = (marks j : AddCircle L)}
  have hS : S.Countable := CircleSingularity.countable_marked_lifts marks
  have hgood : ∀ᵐ t : ℝ, ∀ j, (t : AddCircle L) ≠ (marks j : AddCircle L) := by
    have hn : ∀ᵐ t : ℝ, t ∉ S := (measure_eq_zero_iff_ae_notMem).mp (hS.measure_zero volume)
    simpa only [S, mem_ofPred_eq, not_exists] using hn
  let G := fun t : ℝ => A * (1 + ∑ j, dist (t : AddCircle L) (marks j : AddCircle L) ^ (-γ))
  have hGi (u v : ℝ) : IntervalIntegrable G volume u v := by
    apply IntervalIntegrable.const_mul _ A
    apply IntervalIntegrable.add intervalIntegrable_const
    have hj (j : ι) : IntervalIntegrable
        (fun t : ℝ => dist (t : AddCircle L) (marks j : AddCircle L) ^ (-γ)) volume u v := by
      have hi := locallyIntegrable_translate_sub
        (locallyIntegrable_circle_dist_rpow (Fact.out : 0 < L) (by linarith : -1 < -γ)) (marks j)
      simpa only [AddCircle.coe_sub, dist_eq_norm, sub_zero] using
        (hi.integrableOn_isCompact isCompact_uIcc).intervalIntegrable (a := u) (b := v)
    simpa only [Finset.sum_fn] using IntervalIntegrable.sum Finset.univ (fun j _ => hj j)
  have hbound (t : ℝ) (ht : ∀ j, (t : AddCircle L) ≠ (marks j : AddCircle L)) :
      |deriv f t| ≤ G t := (hderiv t ht).2.trans
    (mul_le_mul_of_nonneg_left (cappedMarkDistance_rpow_le_one_add_sum
      (fun j => (marks j : AddCircle L)) (t : AddCircle L) (-γ)) hA)
  have hdi (u v : ℝ) : IntervalIntegrable (deriv f) volume u v := by
    refine (hGi u v).mono_fun (measurable_deriv f).aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_of_ae hgood] with t ht
    rw [Real.norm_eq_abs, Real.norm_of_nonneg (show 0 ≤ G t by dsimp [G]; positivity)]
    exact hbound t ht
  have hordered (u v : ℝ) (huv : u < v) (hvL : v - u ≤ L) (hv1 : v - u ≤ 1) :
      |f v - f u| ≤ A * (1 + (Fintype.card ι : ℝ) * (1 + 2 / (1 - γ))) * (v - u) ^ (1 - γ) := by
    have hv : 0 < v - u := sub_pos.mpr huv
    have hFTC := integral_eq_of_hasDerivAt_off_countable f (deriv f) hS hc.continuousOn
      (fun t ht => (hderiv t (by simpa only [S, mem_ofPred_eq, not_exists] using ht.2)).1.hasDerivAt)
      (hdi u v)
    have hb := intervalIntegral.norm_integral_le_of_norm_le huv.le
      (show ∀ᵐ t : ℝ, t ∈ Ioc u v → ‖deriv f t‖ ≤ G t from by
        filter_upwards [hgood] with t ht _
        simpa only [Real.norm_eq_abs] using hbound t ht) (hGi u v)
    rw [hFTC, Real.norm_eq_abs] at hb
    apply hb.trans
    have hsumI (j : ι) : IntervalIntegrable
        (fun t : ℝ => dist (t : AddCircle L) (marks j : AddCircle L) ^ (-γ)) volume u v := by
      have hi := locallyIntegrable_translate_sub
        (locallyIntegrable_circle_dist_rpow (Fact.out : 0 < L) (by linarith : -1 < -γ)) (marks j)
      simpa only [AddCircle.coe_sub, dist_eq_norm, sub_zero] using
        (hi.integrableOn_isCompact isCompact_uIcc).intervalIntegrable (a := u) (b := v)
    have hsingle (j : ι) :
        (∫ t in u..v, dist (t : AddCircle L) (marks j : AddCircle L) ^ (-γ)) ≤
          (1 + 2 / (1 - γ)) * (v - u) ^ (1 - γ) := by
      have hb := integral_circle_power_short_interval_le (Fact.out : 0 < L) hγ0 hγ1 huv hvL (marks j)
      simpa only [← dist_coe_zero_eq_circDist, AddCircle.coe_sub, dist_eq_norm, sub_zero] using hb
    have hlen : v - u ≤ (v - u) ^ (1 - γ) := by
      have hp : (v - u) ^ γ ≤ 1 := Real.rpow_le_one hv.le hv1 hγ0
      calc v - u = (v - u) ^ (1 - γ) * (v - u) ^ γ := by
            rw [← Real.rpow_add hv]
            simp
        _ ≤ _ := mul_le_of_le_one_right (by positivity) hp
    have hsum : IntervalIntegrable (fun t : ℝ => ∑ j,
        dist (t : AddCircle L) (marks j : AddCircle L) ^ (-γ)) volume u v := by
      simpa only [Finset.sum_fn] using IntervalIntegrable.sum Finset.univ (fun j _ => hsumI j)
    dsimp only [G]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add intervalIntegrable_const hsum,
      intervalIntegral.integral_const, smul_eq_mul, mul_one,
      intervalIntegral.integral_finsetSum (fun j _ => hsumI j)]
    apply (mul_le_mul_of_nonneg_left (add_le_add hlen (Finset.sum_le_sum (fun j _ => hsingle j))) hA).trans_eq
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · rw [abs_of_pos (sub_pos.mpr hxy)] at *
    exact hordered x y hxy hshort hsmall
  · subst y
    simp only [sub_self, abs_zero, Real.zero_rpow (by linarith : 1 - γ ≠ 0), mul_zero, le_refl]
  · rw [abs_sub_comm y x, abs_of_pos (sub_pos.mpr hxy)] at hshort hsmall ⊢
    rw [abs_sub_comm (f y) (f x)]
    exact hordered y x hxy hshort hsmall

/-- The smoothing error of the continuous extension, including at the marks. -/
theorem circleMollify_sub_le_of_marked_integrable_deriv {L γ A : ℝ} [Fact (0 < L)]
    (hL : 1 ≤ L) {ι : Type*} [Fintype ι] [Nonempty ι] (marks : ι → ℝ)
    {ρ f : ℝ → ℝ} (hρ : IsMollifier ρ) (hc : Continuous f) (hp : Function.Periodic f L)
    (hA : 0 ≤ A) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hderiv : ∀ x : ℝ, (∀ j, (x : AddCircle L) ≠ (marks j : AddCircle L)) →
      DifferentiableAt ℝ f x ∧ |deriv f x| ≤ A *
        cappedMarkDistance (fun j => (marks j : AddCircle L)) (x : AddCircle L) ^ (-γ))
    {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (x : ℝ) :
    |f x - circleMollify ρ L h f x| ≤
      A * (1 + (Fintype.card ι : ℝ) * (1 + 2 / (1 - γ))) * h ^ (1 - γ) := by
  let K := A * (1 + (Fintype.card ι : ℝ) * (1 + 2 / (1 - γ)))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hH (u : ℝ) (hu : |u| ≤ h / 2) : |f (x - u) - f x| ≤ K * |u| ^ (1 - γ) := by
    have hv := finiteMark_holder_of_deriv marks hc hA hγ0 hγ1 hderiv
      (x := x) (y := x - u)
      (by simpa only [sub_sub_cancel_left, abs_neg] using
        (show |u| ≤ L by linarith))
      (by simpa only [sub_sub_cancel_left, abs_neg] using
        (show |u| ≤ 1 by linarith))
    simpa only [sub_sub_cancel_left, abs_neg] using hv
  have hv := circleMollify_sub_le_of_holder hρ (Fact.out : 0 < L) hh hc.locallyIntegrable hp hK
    (by linarith : 0 ≤ 1 - γ) x hH
  rw [abs_sub_comm] at hv
  exact hv.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (by positivity) (by linarith : h / 2 ≤ h) (by linarith : 0 ≤ 1 - γ)) hK)

end Riesz1
