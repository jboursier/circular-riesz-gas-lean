/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.CircleMollifyError
public import Riesz1.ToMathlib.FiniteMarkDistanceLocal
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Smoothing errors off a finite set of marks

A derivative envelope yields a local error `C h r^(-1-α)` whenever
`h ≤ r`. In particular the error is `O(h)` on every fixed region away
from the marks, without needing values or continuity at the marks.
-/

public section

open MeasureTheory Set Filter Topology

namespace Riesz1

/-- Local smoothing error from a marked derivative envelope. Integrability
is required globally. Differentiability and its bound are required only off the marks. -/
theorem circleMollify_sub_le_of_marked_deriv {L : ℝ} [Fact (0 < L)]
    {ι : Type*} [Fintype ι] [Nonempty ι] (marks : ι → ℝ)
    {ρ f : ℝ → ℝ} (hρ : IsMollifier ρ) (hf : LocallyIntegrable f volume)
    (hp : Function.Periodic f L) {A α : ℝ} (hA : 0 ≤ A) (hα : -1 ≤ α)
    (hderiv : ∀ x : ℝ, (∀ j, (x : AddCircle L) ≠ (marks j : AddCircle L)) →
      DifferentiableAt ℝ f x ∧ |deriv f x| ≤ A *
        cappedMarkDistance (fun j => (marks j : AddCircle L)) (x : AddCircle L) ^ (-1 - α))
    {h x : ℝ} (hh : 0 < h)
    (hx : ∀ j, (x : AddCircle L) ≠ (marks j : AddCircle L))
    (hhr : h ≤ cappedMarkDistance (fun j => (marks j : AddCircle L)) (x : AddCircle L)) :
    |f x - circleMollify ρ L h f x| ≤
      A * (1 / 2 : ℝ) ^ (-1 - α) * h *
        cappedMarkDistance (fun j => (marks j : AddCircle L)) (x : AddCircle L) ^ (-1 - α) := by
  let r := cappedMarkDistance (fun j => (marks j : AddCircle L)) (x : AddCircle L)
  have hr : 0 < r := cappedMarkDistance_pos _ _ hx
  have hr1 : r ≤ 1 := cappedMarkDistance_le_one _ _
  let M := A * (r / 2) ^ (-1 - α)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hH (u : ℝ) (hu : |u| ≤ h / 2) : |f (x - u) - f x| ≤ M * |u| ^ (1 : ℝ) := by
    have hdist (z : ℝ) (hz : z ∈ uIcc x (x - u)) :
        r / 2 ≤ cappedMarkDistance (fun j => (marks j : AddCircle L)) (z : AddCircle L) := by
      apply le_cappedMarkDistance_of_dist (fun j => (marks j : AddCircle L))
        (x := (x : AddCircle L)) (r := r) (by linarith) le_rfl
      have hz' : |z - x| ≤ |u| := by
        simpa only [sub_sub_cancel_left, abs_neg] using abs_sub_left_of_mem_uIcc hz
      have hc : dist (x : AddCircle L) (z : AddCircle L) ≤ |x - z| := by
        rw [dist_eq_norm, ← AddCircle.coe_sub]
        exact (QuotientAddGroup.norm_mk_le_norm (m := x - z)
          (S := AddSubgroup.zmultiples L)).trans_eq (Real.norm_eq_abs _)
      rw [abs_sub_comm] at hc
      linarith
    have hgood (z : ℝ) (hz : z ∈ uIcc x (x - u)) :
        ∀ j, (z : AddCircle L) ≠ (marks j : AddCircle L) := by
      intro j hj
      have hd := (hdist z hz).trans (cappedMarkDistance_le_dist _ _ j)
      rw [hj, dist_self] at hd
      linarith
    have hb (z : ℝ) (hz : z ∈ uIcc x (x - u)) : ‖deriv f z‖ ≤ M := by
      rw [Real.norm_eq_abs]
      exact (hderiv z (hgood z hz)).2.trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos
          (by positivity) (hdist z hz) (by linarith)) hA)
    have hv := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun z hz => (hderiv z (hgood z hz)).1) hb (convex_uIcc x (x - u))
      left_mem_uIcc right_mem_uIcc
    simpa only [Real.norm_eq_abs, sub_sub_cancel_left, abs_neg, Real.rpow_one] using hv
  have hv := circleMollify_sub_le_of_holder hρ (Fact.out : 0 < L) hh hf hp hM
    (by norm_num : (0 : ℝ) ≤ 1) x hH
  rw [abs_sub_comm, Real.rpow_one] at hv
  calc _ ≤ M * (h / 2) := hv
    _ ≤ M * h := mul_le_mul_of_nonneg_left (by linarith) hM
    _ = _ := by
      dsimp [M]
      rw [show r / 2 = (1 / 2 : ℝ) * r by ring, Real.mul_rpow (by norm_num) hr.le]
      ring

/-- The local value estimate implies the transition bound, in fact on all
`r ≥ h`. This is numerical and has no additional regularity assumptions. -/
theorem marked_local_error_transition {v C h r α : ℝ} (hC : 0 ≤ C)
    (hh : 0 < h) (hhr : h ≤ r) (hα : -1 ≤ α)
    (hv : |v| ≤ C * h * r ^ (-1 - α)) : |v| ≤ C * h ^ (-α) := by
  have hp := Real.rpow_le_rpow_of_nonpos hh hhr (by linarith : -1 - α ≤ 0)
  have he : h * h ^ (-1 - α) = h ^ (-α) := by
    conv_lhs => lhs; rw [← Real.rpow_one h]
    rw [← Real.rpow_add hh]
    congr 1
    ring
  apply hv.trans
  calc C * h * r ^ (-1 - α) ≤ C * h * h ^ (-1 - α) :=
        mul_le_mul_of_nonneg_left hp (mul_nonneg hC hh.le)
    _ = _ := by rw [mul_assoc, he]

/-- The same estimate is `O(h)` uniformly wherever `r ≥ δ > 0`. -/
theorem marked_local_error_away {v C h r δ α : ℝ} (hC : 0 ≤ C)
    (hh : 0 ≤ h) (hδ : 0 < δ) (hδr : δ ≤ r) (hα : -1 ≤ α)
    (hv : |v| ≤ C * h * r ^ (-1 - α)) : |v| ≤ (C * δ ^ (-1 - α)) * h := by
  apply hv.trans
  calc C * h * r ^ (-1 - α) ≤ C * h * δ ^ (-1 - α) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos hδ hδr (by linarith)) (mul_nonneg hC hh)
    _ = _ := by ring

end Riesz1
