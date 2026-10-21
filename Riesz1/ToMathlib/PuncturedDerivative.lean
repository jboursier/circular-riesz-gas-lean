/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
/-!
# Integrability and absolute continuity at a puncture

The derivative estimate is locally a power bound
`|q'(x)| ≤ C x^(-1-b)`, with `0 ≤ b < 1`. On a positive half interval, integration
bounds `q` by a multiple of `x^(-b)` when `b > 0`, proving integrability up to zero.
A continuous primitive is consequently absolutely continuous. For `b = 0`, slightly
increasing the exponent avoids a separate logarithmic calculation.

These are general real-variable lemmas. Applying them simultaneously at the marked points
of the transport requires additional localization and representative arguments.
-/

public section

open MeasureTheory Set intervalIntegral
namespace Riesz1.PuncturedDerivative
/-- Integrating the derivative bound from an interior point gives a power bound. -/
theorem abs_le_rpow_of_deriv_bound {q : ℝ → ℝ} {b C R : ℝ} (hb : 0 < b) (hC : 0 ≤ C)
    (hR : 0 < R) (hq : ∀ x ∈ Ioc 0 R, DifferentiableAt ℝ q x)
    (hbound : ∀ x ∈ Ioc 0 R, |deriv q x| ≤ C * x ^ (-1 - b))
    {x : ℝ} (hx : x ∈ Ioc 0 R) :
    |q x| ≤ |q R| + C / b * x ^ (-b) := by
  have hp : IntervalIntegrable (fun t : ℝ => t ^ (-1 - b)) volume x R := by
    apply intervalIntegrable_rpow
    right
    rw [uIcc_of_le hx.2]
    exact fun h => not_lt_of_ge h.1 hx.1
  have hdc : ContinuousOn q (Icc x R) := by
    intro t ht
    exact (hq t ⟨lt_of_lt_of_le hx.1 ht.1, ht.2⟩).continuousAt.continuousWithinAt
  have hd : IntervalIntegrable (deriv q) volume x R := by
    apply (hp.const_mul C).mono_fun (measurable_deriv q).aestronglyMeasurable.restrict
    rw [uIoc_of_le hx.2]
    exact ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => by
      dsimp only
      rw [Real.norm_eq_abs, Real.norm_of_nonneg (mul_nonneg hC (Real.rpow_nonneg (by linarith [ht.1, hx.1]) _))]
      exact hbound t ⟨lt_trans hx.1 ht.1, ht.2⟩
  have hFTC := integral_eq_sub_of_hasDerivAt_of_le hx.2 hdc
    (fun t ht => (hq t ⟨lt_trans hx.1 ht.1, ht.2.le⟩).hasDerivAt) hd
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le hx.2
    (ae_of_all volume fun t (ht : t ∈ Ioc x R) => by
      rw [Real.norm_eq_abs]
      exact hbound t ⟨lt_trans hx.1 ht.1, ht.2⟩) (hp.const_mul C)
  have hval : ∫ t in x..R, C * t ^ (-1 - b) = C / b * (x ^ (-b) - R ^ (-b)) := by
    rw [intervalIntegral.integral_const_mul, integral_rpow]
    · have he : -1 - b + 1 = -b := by ring
      rw [he]
      field_simp
      ring
    · right
      constructor
      · linarith
      · rw [uIcc_of_le hx.2]
        exact fun h => not_lt_of_ge h.1 hx.1
  rw [hFTC, Real.norm_eq_abs, hval] at hnorm
  have htri := abs_add_le (q x - q R) (q R)
  have hcpos : 0 ≤ C / b := div_nonneg hC hb.le
  have hrpos : 0 ≤ R ^ (-b) := Real.rpow_nonneg hR.le _
  simp only [sub_add_cancel] at htri
  rw [abs_sub_comm (q x) (q R)] at htri
  nlinarith
/-- A power singularity of the derivative of order `1 + b`, with `0 < b < 1`,
gives integrability of the function across the left endpoint. -/
theorem integrableOn_of_deriv_rpow_bound {q : ℝ → ℝ} {b C R : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (hC : 0 ≤ C) (hR : 0 < R) (hq : ∀ x ∈ Ioc 0 R, DifferentiableAt ℝ q x)
    (hbound : ∀ x ∈ Ioc 0 R, |deriv q x| ≤ C * x ^ (-1 - b)) :
    IntegrableOn q (Ioc 0 R) := by
  have hm : AEStronglyMeasurable q (volume.restrict (Ioc 0 R)) :=
    (show ContinuousOn q (Ioc 0 R) from fun x hx => (hq x hx).continuousAt.continuousWithinAt).aestronglyMeasurable measurableSet_Ioc
  have hdom : IntegrableOn (fun x : ℝ => |q R| + C / b * x ^ (-b)) (Ioc 0 R) := by
    have hp : IntegrableOn (fun x : ℝ => x ^ (-b)) (Ioc 0 R) :=
      ((intervalIntegrable_rpow' (a := 0) (b := R) (by linarith : -1 < -b)).1)
    exact (integrableOn_const (s := Ioc 0 R) (μ := volume) (by simp)).add (hp.const_mul _)
  refine Integrable.mono' hdom hm (ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => ?_)
  rw [Real.norm_eq_abs]
  exact abs_le_rpow_of_deriv_bound hb hC hR hq hbound hx
/-- A continuous function whose second derivative has the given punctured power bound
has an integrable first derivative and is absolutely continuous up to the puncture. -/
theorem absolutelyContinuousOnInterval_of_second_deriv_bound {f : ℝ → ℝ} {b C R : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (hC : 0 ≤ C) (hR : 0 < R) (hc : ContinuousOn f (Icc 0 R))
    (hd : ∀ x ∈ Ioc 0 R, DifferentiableAt ℝ f x)
    (hd2 : ∀ x ∈ Ioc 0 R, DifferentiableAt ℝ (deriv f) x)
    (hbound : ∀ x ∈ Ioc 0 R, |deriv (deriv f) x| ≤ C * x ^ (-1 - b)) :
    IntervalIntegrable (deriv f) volume 0 R ∧ AbsolutelyContinuousOnInterval f 0 R := by
  have hi : IntervalIntegrable (deriv f) volume 0 R := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le]
    exact integrableOn_of_deriv_rpow_bound hb hb1 hC hR hd2 hbound
  refine ⟨hi, ?_⟩
  have hzero : (0 : ℝ) ∈ uIcc 0 R := by rw [uIcc_of_le hR.le]; exact ⟨le_rfl, hR.le⟩
  have hAC := hi.absolutelyContinuousOnInterval_intervalIntegral hzero
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => f 0) 0 R :=
    (LipschitzWith.lipschitzOnWith (LipschitzWith.const (f 0))).absolutelyContinuousOnInterval
  apply (hconst.add hAC).congr
  intro x hx
  rw [uIcc_of_le hR.le] at hx
  have hix : IntervalIntegrable (deriv f) volume 0 x := hi.mono_set (by
    rw [uIcc_of_le hx.1, uIcc_of_le hR.le]
    exact Icc_subset_Icc le_rfl hx.2)
  have he := integral_eq_sub_of_hasDerivAt_of_le hx.1
    (hc.mono (Icc_subset_Icc le_rfl hx.2))
    (fun t ht => (hd t ⟨ht.1, ht.2.le.trans hx.2⟩).hasDerivAt) hix
  change f 0 + (∫ t in (0 : ℝ)..x, deriv f t) = f x
  rw [he]
  ring
/-- The same conclusion for `0 ≤ b < 1`, including the logarithmic endpoint `b = 0`.
On a half interval of length at most one, increasing the exponent stays below one. -/
theorem absolutelyContinuousOnInterval_of_second_deriv_bound_nonneg {f : ℝ → ℝ} {b C R : ℝ} (hb : 0 ≤ b) (hb1 : b < 1)
    (hC : 0 ≤ C) (hR : 0 < R) (hR1 : R ≤ 1) (hc : ContinuousOn f (Icc 0 R))
    (hd : ∀ x ∈ Ioc 0 R, DifferentiableAt ℝ f x)
    (hd2 : ∀ x ∈ Ioc 0 R, DifferentiableAt ℝ (deriv f) x)
    (hbound : ∀ x ∈ Ioc 0 R, |deriv (deriv f) x| ≤ C * x ^ (-1 - b)) :
    IntervalIntegrable (deriv f) volume 0 R ∧ AbsolutelyContinuousOnInterval f 0 R := by
  let b' : ℝ := (b + 1) / 2
  have hb' : 0 < b' := by dsimp [b']; linarith
  have hb'1 : b' < 1 := by dsimp [b']; linarith
  apply absolutelyContinuousOnInterval_of_second_deriv_bound hb' hb'1 hC hR hc hd hd2
  intro x hx
  apply (hbound x hx).trans
  apply mul_le_mul_of_nonneg_left _ hC
  exact Real.rpow_le_rpow_of_exponent_ge hx.1 (hx.2.trans hR1) (by dsimp [b']; linarith)
end Riesz1.PuncturedDerivative
