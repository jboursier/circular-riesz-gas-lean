/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.WeightedSobolev.LipschitzClip
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Smooth approximations of clipping

Differences of regularized absolute values give smooth contractions
fixing zero and converging to clipping at `±R`.
-/

@[expose] public section

noncomputable section

open Filter Topology
open scoped ContDiff

namespace Riesz1.WeightedSobolev

/-- Regularized absolute value. -/
def smoothAbs (ε r : ℝ) : ℝ := Real.sqrt (r ^ 2 + ε ^ 2)

theorem contDiff_smoothAbs {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ ∞ (smoothAbs ε) :=
  (contDiff_id.pow 2 |>.add contDiff_const).sqrt (fun r => by
    change r ^ 2 + ε ^ 2 ≠ 0
    positivity)

theorem deriv_smoothAbs {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    deriv (smoothAbs ε) r = r / Real.sqrt (r ^ 2 + ε ^ 2) := by
  have hd0 : HasDerivAt (fun x : ℝ => x ^ 2 + ε ^ 2) (2 * r) r := by
    convert ((hasDerivAt_id r).pow 2).add_const (ε ^ 2) using 1 <;> simp
  have hd : HasDerivAt (smoothAbs ε) ((2 * r) / (2 * Real.sqrt (r ^ 2 + ε ^ 2))) r :=
    hd0.sqrt (by positivity)
  rw [hd.deriv]
  ring

theorem norm_deriv_smoothAbs_le {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    ‖deriv (smoothAbs ε) r‖ ≤ 1 := by
  rw [deriv_smoothAbs hε, norm_div, Real.norm_eq_abs,
    Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  apply (div_le_one (Real.sqrt_pos.mpr (by positivity))).mpr
  have hs := Real.sq_sqrt (show 0 ≤ r ^ 2 + ε ^ 2 by positivity)
  nlinarith [Real.sqrt_nonneg (r ^ 2 + ε ^ 2), sq_abs r, abs_nonneg r, sq_nonneg ε]

/-- Smooth clipping, with the same origin and derivative bound as exact clipping. -/
def smoothClip (R ε r : ℝ) : ℝ := (smoothAbs ε (r + R) - smoothAbs ε (r - R)) / 2

theorem contDiff_smoothClip (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ∞ (smoothClip R ε) :=
  ((contDiff_smoothAbs hε).comp (contDiff_id.add contDiff_const) |>.sub
    ((contDiff_smoothAbs hε).comp (contDiff_id.sub contDiff_const))).div_const 2

theorem smoothClip_zero (R ε : ℝ) : smoothClip R ε 0 = 0 := by
  simp [smoothClip, smoothAbs]

theorem deriv_smoothClip (R : ℝ) {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    deriv (smoothClip R ε) r =
      (deriv (smoothAbs ε) (r + R) - deriv (smoothAbs ε) (r - R)) / 2 := by
  have h1 : HasDerivAt (fun x => smoothAbs ε (x + R)) (deriv (smoothAbs ε) (r + R)) r := by
    simpa only [Function.comp_def, id_eq, mul_one] using
      ((contDiff_smoothAbs hε).differentiable (by norm_num) (r + R)).hasDerivAt.comp r
        ((hasDerivAt_id r).add_const R)
  have h2 : HasDerivAt (fun x => smoothAbs ε (x - R)) (deriv (smoothAbs ε) (r - R)) r := by
    simpa only [Function.comp_def, id_eq, mul_one] using
      ((contDiff_smoothAbs hε).differentiable (by norm_num) (r - R)).hasDerivAt.comp r
        ((hasDerivAt_id r).sub_const R)
  have hd : HasDerivAt (smoothClip R ε)
      ((deriv (smoothAbs ε) (r + R) - deriv (smoothAbs ε) (r - R)) / 2) r :=
    (h1.sub h2).div_const 2
  exact hd.deriv

theorem norm_deriv_smoothClip_le (R : ℝ) {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    ‖deriv (smoothClip R ε) r‖ ≤ 1 := by
  rw [deriv_smoothClip R hε, norm_div, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have h := norm_sub_le (deriv (smoothAbs ε) (r + R)) (deriv (smoothAbs ε) (r - R))
  have h1 := norm_deriv_smoothAbs_le hε (r + R)
  have h2 := norm_deriv_smoothAbs_le hε (r - R)
  linarith

theorem tendsto_smoothAbs (r : ℝ) :
    Tendsto (fun k : ℕ => smoothAbs (1 / (k + 1)) r) atTop (𝓝 |r|) := by
  have ht := (tendsto_const_nhds (x := r ^ 2)).add ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2)
  simpa only [smoothAbs, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero,
    Real.sqrt_sq_eq_abs] using ht.sqrt

theorem clipReal_eq_abs (R : ℝ) (hR : 0 ≤ R) (r : ℝ) :
    clipReal R r = (|r + R| - |r - R|) / 2 := by
  rcases le_total r (-R) with hr | hr
  · rw [clipReal, min_eq_right (by linarith : r ≤ R), max_eq_left hr,
      abs_of_nonpos (by linarith : r + R ≤ 0), abs_of_nonpos (by linarith : r - R ≤ 0)]
    ring
  · rcases le_total r R with hr' | hr'
    · rw [clipReal, min_eq_right hr', max_eq_right hr, abs_of_nonneg (by linarith : 0 ≤ r + R),
        abs_of_nonpos (by linarith : r - R ≤ 0)]
      ring
    · rw [clipReal, min_eq_left hr', max_eq_right (by linarith : -R ≤ R),
        abs_of_nonneg (by linarith : 0 ≤ r + R), abs_of_nonneg (by linarith : 0 ≤ r - R)]
      ring

theorem tendsto_smoothClip {R : ℝ} (hR : 0 ≤ R) (r : ℝ) :
    Tendsto (fun k : ℕ => smoothClip R (1 / (k + 1)) r) atTop (𝓝 (clipReal R r)) := by
  rw [clipReal_eq_abs R hR]
  exact ((tendsto_smoothAbs (r + R)).sub (tendsto_smoothAbs (r - R))).div_const 2

/-- Away from zero the derivative of the regularized absolute value tends to the sign. -/
theorem tendsto_deriv_smoothAbs {r : ℝ} (hr : r ≠ 0) :
    Tendsto (fun k : ℕ => deriv (smoothAbs (1 / (k + 1))) r)
      atTop (𝓝 (r / |r|)) := by
  have he (k : ℕ) : deriv (smoothAbs (1 / (k + 1))) r = r / smoothAbs (1 / (k + 1)) r :=
    deriv_smoothAbs (by positivity) r
  simp only [he]
  exact tendsto_const_nhds.div (tendsto_smoothAbs r) (abs_ne_zero.mpr hr)

/-- At points distinct from the two clipping thresholds the derivatives tend to the strict
sublevel indicator. -/
theorem tendsto_deriv_smoothClip {R r : ℝ} (hR : 0 ≤ R) (hr1 : r ≠ -R) (hr2 : r ≠ R) :
    Tendsto (fun k : ℕ => deriv (smoothClip R (1 / (k + 1))) r)
      atTop (𝓝 (if |r| < R then (1 : ℝ) else 0)) := by
  have h1 : r + R ≠ 0 := by intro h; apply hr1; linarith
  have h2 : r - R ≠ 0 := sub_ne_zero.mpr hr2
  have he (k : ℕ) : deriv (smoothClip R (1 / (k + 1))) r =
      (deriv (smoothAbs (1 / (k + 1))) (r + R) -
        deriv (smoothAbs (1 / (k + 1))) (r - R)) / 2 := deriv_smoothClip R (by positivity) r
  have ht := ((tendsto_deriv_smoothAbs h1).sub (tendsto_deriv_smoothAbs h2)).div_const 2
  have hv : ((r + R) / |r + R| - (r - R) / |r - R|) / 2 =
      if |r| < R then 1 else 0 := by
    by_cases hr : |r| < R
    · rw [ite_eq_left hr, abs_of_pos (by linarith [(abs_lt.mp hr).1]),
        abs_of_neg (by linarith [(abs_lt.mp hr).2]), div_self h1, div_neg, div_self h2]
      norm_num
    · rw [ite_eq_right hr]
      have hor : r < -R ∨ R < r := by
        rcases le_total r (-R) with hl | hl
        · exact Or.inl (lt_of_le_of_ne hl hr1)
        · right
          by_contra hrr
          have hh : r < R := lt_of_le_of_ne (le_of_not_gt hrr) hr2
          exact hr (abs_lt.mpr ⟨lt_of_le_of_ne hl (Ne.symm hr1), hh⟩)
      rcases hor with hl | hl
      · rw [abs_of_neg (by linarith : r + R < 0),
          abs_of_neg (by linarith : r - R < 0), div_neg, div_self h1, div_neg, div_self h2]
        norm_num
      · rw [abs_of_pos (by linarith : 0 < r + R), abs_of_pos (by linarith : 0 < r - R),
          div_self h1, div_self h2]
        norm_num
  simpa only [he, hv] using ht

end Riesz1.WeightedSobolev

end
