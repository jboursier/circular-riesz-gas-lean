/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# A periodic function is bounded by the integral of its derivative majorant

First step of Lemma 5.2: a real `C¹` function `f` of period `L`
with `f (L / 2) = 0` satisfies, at every point `u` of `[-L/2, L/2]`,
`|f u| ≤ ∫_{|u|}^{L/2} B`, whenever `|f'(t)| ≤ B |t|` for almost every `t` in `[-L/2, L/2]`.
The integral runs from the point `|u|` to the half period, along the arc on the side of `u`.
-/

@[expose] public section

open MeasureTheory Set

namespace Riesz1

/-- **Periodic tail bound.** Let `f` be `C¹` with period `L > 0` and `f (L / 2) = 0`. Let
`B` be integrable on `[0, L/2]`, and suppose `|f'(t)| ≤ B |t|` for almost every `t` in
`[-L/2, L/2]`. Then every `u` in `[-L/2, L/2]` satisfies `|f u| ≤ ∫_{|u|}^{L/2} B`. -/
theorem abs_le_intervalIntegral_of_periodic {L : ℝ} (hL : 0 < L) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hper : Function.Periodic f L) (hzero : f (L / 2) = 0)
    {B : ℝ → ℝ} (hBi : IntervalIntegrable B volume 0 (L / 2))
    (hB : ∀ᵐ t ∂volume, t ∈ Icc (-(L / 2)) (L / 2) → |deriv f t| ≤ B |t|)
    {u : ℝ} (hu : u ∈ Icc (-(L / 2)) (L / 2)) :
    |f u| ≤ ∫ t in |u|..(L / 2), B t := by
  have hdiff : ∀ x, HasDerivAt f (deriv f x) x := fun x =>
    ((hf.differentiable one_ne_zero) x).hasDerivAt
  have hcont : Continuous (deriv f) := hf.continuous_deriv_one
  rcases le_total 0 u with hu0 | hu0
  · -- The arc from `u` to `L/2`, where `|t| = t`.
    rw [abs_of_nonneg hu0]
    have hFTC : ∫ t in u..(L / 2), deriv f t = f (L / 2) - f u :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hdiff x)
        (hcont.intervalIntegrable _ _)
    have hBsub : IntervalIntegrable B volume u (L / 2) := by
      refine hBi.mono_set ?_
      rw [uIcc_of_le hu.2, uIcc_of_le (by linarith [hu.2, hu0] : (0 : ℝ) ≤ L / 2)]
      exact Icc_subset_Icc hu0 le_rfl
    have hae : ∀ᵐ t ∂volume, t ∈ Ioc u (L / 2) → ‖deriv f t‖ ≤ B t := by
      filter_upwards [hB] with t ht hmem
      have htI : t ∈ Icc (-(L / 2)) (L / 2) := ⟨by linarith [hmem.1, hu.1], hmem.2⟩
      have ht0 : (0 : ℝ) ≤ t := by linarith [hmem.1]
      have h := ht htI
      rw [abs_of_nonneg ht0] at h
      rw [Real.norm_eq_abs]
      exact h
    have hbound := intervalIntegral.norm_integral_le_of_norm_le hu.2 hae hBsub
    rw [Real.norm_eq_abs] at hbound
    have hfu : f u = -∫ t in u..(L / 2), deriv f t := by
      rw [hFTC, hzero]
      ring
    rw [hfu, abs_neg]
    exact hbound
  · -- The arc from `-L/2` to `u`, where `|t| = -t`, reflected to `[|u|, L/2]`.
    have hf0 : f (-(L / 2)) = 0 := by
      have h := hper (-(L / 2))
      rw [show -(L / 2) + L = L / 2 by ring, hzero] at h
      exact h.symm
    rw [abs_of_nonpos hu0]
    have hFTC : ∫ t in (-(L / 2))..u, deriv f t = f u - f (-(L / 2)) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hdiff x)
        (hcont.intervalIntegrable _ _)
    have hBsub : IntervalIntegrable (fun t => B (-t)) volume (-(L / 2)) u := by
      rw [IntervalIntegrable.iff_comp_neg]
      simp only [neg_neg]
      refine hBi.mono_set (uIcc_subset_uIcc ?_ ?_) <;> rw [Set.mem_uIcc] <;>
        exact Or.inl ⟨by linarith [hu0], by linarith [hu.1]⟩
    have hae : ∀ᵐ t ∂volume, t ∈ Ioc (-(L / 2)) u → ‖deriv f t‖ ≤ B (-t) := by
      filter_upwards [hB] with t ht hmem
      have htI : t ∈ Icc (-(L / 2)) (L / 2) := ⟨hmem.1.le, by linarith [hmem.2, hu0]⟩
      have ht0 : t ≤ 0 := by linarith [hmem.2]
      have h := ht htI
      rw [abs_of_nonpos ht0] at h
      rw [Real.norm_eq_abs]
      exact h
    have hbound := intervalIntegral.norm_integral_le_of_norm_le (by linarith [hu.1]) hae hBsub
    rw [Real.norm_eq_abs] at hbound
    have hcomp : ∫ t in (-(L / 2))..u, B (-t) = ∫ t in (-u)..(L / 2), B t := by
      rw [intervalIntegral.integral_comp_neg B, neg_neg]
    have hfu : f u = ∫ t in (-(L / 2))..u, deriv f t := by
      rw [hFTC, hf0, sub_zero]
    rw [hfu]
    rw [hcomp] at hbound
    exact hbound

end Riesz1

end
