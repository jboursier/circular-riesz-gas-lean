/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.FiniteMarkWindow
public import Riesz1.ToMathlib.MollifyLocalDerivative

/-!
# Derivatives of convolutions with finitely many singularities

Near the marks, differentiate the kernel and use the raw window estimate.
Away from every mark, transfer the derivative locally. No integrability of
the original second transport derivative across a mark is required.
-/

public section

open MeasureTheory Set

namespace Riesz1

/-- The derivative estimate for a finite family of singularities. The
constant precedes every circle and the locations of all marks. -/
theorem circleMollify_finiteMark_deriv_bound {ρ : ℝ → ℝ} (hρ : IsMollifier ρ)
    {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1) :
    ∃ D : ℝ, 0 < D ∧ ∀ (L : ℝ), 1 ≤ L →
      ∀ {ι : Type*} [Fintype ι] [Nonempty ι] (marks : ι → ℝ) (C : ℝ), 0 ≤ C →
      ∀ f : ℝ → ℝ, Function.Periodic f L → LocallyIntegrable f volume →
      (∀ᵐ y : ℝ, |f y| ≤ C * (1 + ∑ j, dist (y : AddCircle L) (marks j : AddCircle L) ^ (-b))) →
      (∀ y : ℝ, (∀ j, (y : AddCircle L) ≠ (marks j : AddCircle L)) →
        DifferentiableAt ℝ f y ∧ |deriv f y| ≤ C *
          cappedMarkDistance (fun j => (marks j : AddCircle L)) (y : AddCircle L) ^ (-1 - b)) →
      ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x : ℝ,
        |deriv (circleMollify ρ L h f) x| ≤ D * C * ((Fintype.card ι : ℝ) + 1) *
          (1 + ∑ j, max (dist (x : AddCircle L) (marks j : AddCircle L)) h ^ (-1 - b)) := by
  obtain ⟨A, hA, hwindow⟩ := integral_window_finiteMark_bound hb hb1
  obtain ⟨M, hM, hMbound⟩ := hρ.exists_bound_deriv
  let D := (M + 1) * (A + 1) * (2 : ℝ) ^ (1 + b)
  have hD : 0 < D := by dsimp [D]; positivity
  have hMDA : M * (A + 1) * 2 ^ (1 + b) ≤ D := by
    dsimp [D]
    nlinarith [show 0 < (A + 1) * (2 : ℝ) ^ (1 + b) by positivity]
  have htwoD : (2 : ℝ) ^ (1 + b) ≤ D := by
    dsimp [D]
    nlinarith [show 0 < (2 : ℝ) ^ (1 + b) by positivity]
  refine ⟨D, hD, fun L hL ι _ _ marks C hC f hp hf henv hder h hh hh1 x => ?_⟩
  have hLp : 0 < L := by linarith
  have : Fact (0 < L) := ⟨hLp⟩
  let N : ℝ := Fintype.card ι
  let S := 1 + ∑ j, max (dist (x : AddCircle L) (marks j : AddCircle L)) h ^ (-1 - b)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have he : -1 - b ≤ 0 := by linarith
  rw [show circleMollify ρ L h f = mollifyLine ρ h f from
    funext (circleMollify_eq_mollifyLine hρ hLp hh hf hp)]
  by_cases hfar : ∀ j, 2 * h ≤ dist (x : AddCircle L) (marks j : AddCircle L)
  · let B := C * (1 + ∑ j, (dist (x : AddCircle L) (marks j : AddCircle L) / 2) ^ (-1 - b))
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hlocal (y : ℝ) (hy : |y - x| < h) :
        (∀ j, (y : AddCircle L) ≠ (marks j : AddCircle L)) ∧
        |deriv f y| ≤ B := by
      have hdist (j : ι) : dist (x : AddCircle L) (marks j : AddCircle L) / 2 ≤
          dist (y : AddCircle L) (marks j : AddCircle L) := by
        have ht := dist_triangle (x : AddCircle L) (y : AddCircle L) (marks j : AddCircle L)
        have hxy : dist (x : AddCircle L) (y : AddCircle L) ≤ |y - x| := by
          rw [dist_eq_norm, ← QuotientAddGroup.mk_sub]
          simpa only [Real.norm_eq_abs, abs_sub_comm] using
            (QuotientAddGroup.norm_mk_le_norm (m := x - y) (S := AddSubgroup.zmultiples L))
        linarith [hfar j]
      have hne : ∀ j, (y : AddCircle L) ≠ (marks j : AddCircle L) := by
        intro j heq
        have hj := hdist j
        rw [heq, dist_self] at hj
        linarith [hfar j]
      refine ⟨hne, ((hder y hne).2.trans (mul_le_mul_of_nonneg_left
        (cappedMarkDistance_rpow_le_one_add_sum _ _ _) hC)).trans ?_⟩
      apply mul_le_mul_of_nonneg_left _ hC
      apply add_le_add_right
      apply Finset.sum_le_sum
      intro j _
      exact Real.rpow_le_rpow_of_nonpos (by linarith [hfar j]) (hdist j) he
    have hw := abs_deriv_mollifyLine_le_of_local hρ hh hB hf
      (fun y hy => (hder y (hlocal y hy).1).1) (fun y hy => (hlocal y hy).2)
    have hsum : B ≤ C * 2 ^ (1 + b) * S := by
      have hterms (j : ι) :
          (dist (x : AddCircle L) (marks j : AddCircle L) / 2) ^ (-1 - b) =
            max (dist (x : AddCircle L) (marks j : AddCircle L)) h ^ (-1 - b) * 2 ^ (1 + b) := by
        rw [max_eq_left (by linarith [hfar j])]
        rw [show -1 - b = -(1 + b) by ring, div_two_rpow_neg dist_nonneg]
      have hone : 1 ≤ (2 : ℝ) ^ (1 + b) := Real.one_le_rpow (by norm_num) (by linarith)
      dsimp [B, S]
      simp_rw [hterms]
      rw [← Finset.sum_mul]
      nlinarith [mul_le_mul_of_nonneg_left hone hC]
    change _ ≤ D * C * (N + 1) * S
    refine hw.trans (hsum.trans ?_)
    nlinarith [mul_le_mul_of_nonneg_right htwoD (mul_nonneg hC hS),
      mul_nonneg (show 0 ≤ D * C * S by positivity) hN]
  · obtain ⟨j, hj⟩ := not_forall.mp hfar
    have hj' : dist (x : AddCircle L) (marks j : AddCircle L) ≤ 2 * h := (lt_of_not_ge hj).le
    have hw := hwindow L hL marks C hC f hf henv h hh hh1 x
    have hwin := norm_integral_mul_le_window (g := f) (φ := deriv (scaledMollifier ρ h))
      (x := x) (r := h / 2) hf
      ((contDiff_scaledMollifier hρ).continuous_deriv (by simp))
      (fun u => abs_deriv_scaledMollifier_le hρ hh hMbound u)
      (fun u hu => deriv_scaledMollifier_eq_zero hρ hh hu)
    rw [(hasDerivAt_mollifyLine hρ hh hf x).deriv]
    have hcoef : 1 + N * A ≤ (A + 1) * (N + 1) := by nlinarith
    have hraw : |∫ y, f y * deriv (scaledMollifier ρ h) (x - y)| ≤
        M * C * (A + 1) * (N + 1) * h ^ (-1 - b) := by
      have hw' := hwin.trans (mul_le_mul_of_nonneg_left hw (by positivity))
      have heq : M * (h⁻¹ * h⁻¹) * (C * (1 + N * A) * h ^ (1 - b)) =
          M * C * (1 + N * A) * h ^ (-1 - b) := by
        rw [← inv_mul_inv_mul_rpow_one_sub hh]
        ring
      change _ ≤ M * (h⁻¹ * h⁻¹) * (C * (1 + N * A) * h ^ (1 - b)) at hw'
      rw [heq] at hw'
      refine hw'.trans ?_
      nlinarith [mul_le_mul_of_nonneg_left hcoef
        (show 0 ≤ M * C * h ^ (-1 - b) by positivity)]
    let H := max (dist (x : AddCircle L) (marks j : AddCircle L)) h
    have hH : 0 < H := lt_of_lt_of_le hh (le_max_right _ _)
    have hHle : H ≤ 2 * h := max_le hj' (by linarith)
    have hpow : h ^ (-1 - b) ≤ 2 ^ (1 + b) * H ^ (-1 - b) := by
      have hm := Real.rpow_le_rpow_of_nonpos (by linarith : 0 < H / 2)
        (by linarith : H / 2 ≤ h) he
      have hid : (H / 2) ^ (-1 - b) = H ^ (-1 - b) * 2 ^ (1 + b) := by
        rw [show -1 - b = -(1 + b) by ring, div_two_rpow_neg hH.le]
      rw [hid] at hm
      nlinarith
    have hsingle : H ^ (-1 - b) ≤ S := by
      exact (Finset.single_le_sum (f := fun j =>
        max (dist (x : AddCircle L) (marks j : AddCircle L)) h ^ (-1 - b))
        (fun _ _ => by positivity) (Finset.mem_univ j)).trans (le_add_of_nonneg_left zero_le_one)
    change _ ≤ D * C * (N + 1) * S
    refine hraw.trans ?_
    have hm := mul_le_mul_of_nonneg_left hpow
      (show 0 ≤ M * C * (A + 1) * (N + 1) by positivity)
    have hd := mul_le_mul_of_nonneg_right hMDA
      (show 0 ≤ C * (N + 1) * H ^ (-1 - b) by positivity)
    have hs := mul_le_mul_of_nonneg_left hsingle (show 0 ≤ D * C * (N + 1) by positivity)
    nlinarith

end Riesz1
