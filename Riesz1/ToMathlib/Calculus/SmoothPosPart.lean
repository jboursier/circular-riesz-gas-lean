/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# A smooth approximation of the positive part

For `ε > 0` put `smoothPosPart ε r = (r + √(r² + ε²) − ε) / 2`. This function is smooth, vanishes
at `0`, has derivative in `[0, 1]`, and so is `1`-Lipschitz. It approximates the positive part
`r ↦ max r 0` within `ε`. These are the scalar facts behind the truncation of vector energy
functions in Lemma 3.4.
-/

@[expose] public section

noncomputable section

open Filter Topology
open scoped ContDiff

namespace Riesz1

/-- The smooth approximation `(r + √(r² + ε²) − ε) / 2` of the positive part `max r 0`. -/
def smoothPosPart (ε r : ℝ) : ℝ :=
  (r + Real.sqrt (r ^ 2 + ε ^ 2) - ε) / 2

/-- The approximation vanishes at zero when `ε > 0`. -/
theorem smoothPosPart_zero {ε : ℝ} (hε : 0 < ε) : smoothPosPart ε 0 = 0 := by
  unfold smoothPosPart
  have hsq : (0 : ℝ) ^ 2 + ε ^ 2 = ε ^ 2 := by ring
  rw [hsq, Real.sqrt_sq hε.le]
  ring

/-- The approximation is smooth. -/
theorem contDiff_smoothPosPart (ε : ℝ) (hε : 0 < ε) : ContDiff ℝ ∞ (smoothPosPart ε) := by
  unfold smoothPosPart
  have hpos : ∀ r : ℝ, r ^ 2 + ε ^ 2 ≠ 0 := fun r => by positivity
  have hs : ContDiff ℝ ∞ (fun r : ℝ => Real.sqrt (r ^ 2 + ε ^ 2)) :=
    ((contDiff_id.pow 2).add contDiff_const).sqrt hpos
  exact ((contDiff_id.add hs).sub contDiff_const).div_const 2

/-- The derivative of the approximation. -/
theorem hasDerivAt_smoothPosPart {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    HasDerivAt (smoothPosPart ε) ((1 + r / Real.sqrt (r ^ 2 + ε ^ 2)) / 2) r := by
  have hpos : 0 < r ^ 2 + ε ^ 2 := by positivity
  have hpow : HasDerivAt (fun x : ℝ => x ^ 2) (2 * r) r := by
    simpa using hasDerivAt_pow 2 r
  have hsq : HasDerivAt (fun x : ℝ => x ^ 2 + ε ^ 2) (2 * r) r :=
    HasDerivAt.add_const (ε ^ 2) hpow
  have hs : HasDerivAt (fun x : ℝ => Real.sqrt (x ^ 2 + ε ^ 2))
      (2 * r / (2 * Real.sqrt (r ^ 2 + ε ^ 2))) r :=
    HasDerivAt.sqrt hsq hpos.ne'
  have hsum : HasDerivAt (fun x : ℝ => x + Real.sqrt (x ^ 2 + ε ^ 2) - ε)
      (1 + 2 * r / (2 * Real.sqrt (r ^ 2 + ε ^ 2))) r :=
    ((hasDerivAt_id' r).add hs).sub_const ε
  have hdiv := HasDerivAt.div_const hsum 2
  have heq : (1 + 2 * r / (2 * Real.sqrt (r ^ 2 + ε ^ 2))) / 2 =
      (1 + r / Real.sqrt (r ^ 2 + ε ^ 2)) / 2 := by
    rw [mul_div_mul_left r _ two_ne_zero]
  rw [heq] at hdiv
  exact hdiv

/-- The derivative of the approximation lies in `[0, 1]`, in particular its absolute value is at
most one. -/
theorem abs_deriv_smoothPosPart_le {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    |(1 + r / Real.sqrt (r ^ 2 + ε ^ 2)) / 2| ≤ 1 := by
  have hpos : 0 < Real.sqrt (r ^ 2 + ε ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hr : |r| ≤ Real.sqrt (r ^ 2 + ε ^ 2) :=
    Real.abs_le_sqrt (by nlinarith [sq_nonneg ε])
  have hq : |r / Real.sqrt (r ^ 2 + ε ^ 2)| ≤ 1 := by
    rw [abs_div, abs_of_pos hpos, div_le_one hpos]
    exact hr
  have h1 : |r / Real.sqrt (r ^ 2 + ε ^ 2)| ≤ 1 := hq
  rw [abs_le] at h1 ⊢
  constructor <;> linarith [h1.1, h1.2]

/-- The approximation is `1`-Lipschitz. -/
theorem abs_smoothPosPart_sub_le {ε : ℝ} (hε : 0 < ε) (a b : ℝ) :
    |smoothPosPart ε a - smoothPosPart ε b| ≤ |a - b| := by
  set A := Real.sqrt (a ^ 2 + ε ^ 2) with hAdef
  set B := Real.sqrt (b ^ 2 + ε ^ 2) with hBdef
  have hA2 : A ^ 2 = a ^ 2 + ε ^ 2 := Real.sq_sqrt (by positivity)
  have hB2 : B ^ 2 = b ^ 2 + ε ^ 2 := Real.sq_sqrt (by positivity)
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  -- The product `A B` dominates `a b + ε²`, by comparing squares.
  have hprod : (a * b + ε ^ 2) ^ 2 ≤ (A * B) ^ 2 := by
    rw [mul_pow, hA2, hB2]
    nlinarith [sq_nonneg ((a - b) * ε)]
  have hAB : a * b + ε ^ 2 ≤ A * B := (abs_le_of_sq_le_sq' hprod (by positivity)).2
  -- Hence `(A - B)² ≤ (a - b)²`, which gives `|A - B| ≤ |a - b|`.
  have hsq : (A - B) ^ 2 ≤ (a - b) ^ 2 := by nlinarith [hA2, hB2, hAB]
  have hAB' : |A - B| ≤ |a - b| := sq_le_sq.mp hsq
  unfold smoothPosPart
  rw [← hAdef, ← hBdef]
  have heq : (a + A - ε) / 2 - (b + B - ε) / 2 = ((a - b) + (A - B)) / 2 := by ring
  rw [heq, abs_div, abs_two]
  have h1 := abs_add_le (a - b) (A - B)
  linarith

/-- The approximation vanishes at zero, so it is bounded by the identity in absolute value. -/
theorem abs_smoothPosPart_le {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    |smoothPosPart ε a| ≤ |a| := by
  have h := abs_smoothPosPart_sub_le hε a 0
  rw [smoothPosPart_zero hε, sub_zero, sub_zero] at h
  exact h

/-- The approximation differs from the positive part by at most `ε`. -/
theorem abs_smoothPosPart_sub_max_le {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    |smoothPosPart ε a - max a 0| ≤ ε := by
  set s := Real.sqrt (a ^ 2 + ε ^ 2) with hsdef
  have hs2 : s ^ 2 = a ^ 2 + ε ^ 2 := Real.sq_sqrt (by positivity)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hlow : |a| ≤ s := Real.abs_le_sqrt (by nlinarith [sq_nonneg ε])
  have hup : s ≤ |a| + ε := by
    nlinarith [sq_abs a, abs_nonneg a, sq_nonneg ε, mul_nonneg (abs_nonneg a) hε.le]
  unfold smoothPosPart
  rw [← hsdef]
  rcases le_total 0 a with ha | ha
  · rw [max_eq_left ha, abs_of_nonneg ha] at *
    have h1 : -ε ≤ (a + s - ε) / 2 - a := by linarith [neg_abs_le a]
    have h2 : (a + s - ε) / 2 - a ≤ 0 := by linarith
    rw [abs_le]
    constructor <;> linarith
  · rw [max_eq_right ha, abs_of_nonpos ha] at *
    have h1 : -ε ≤ (a + s - ε) / 2 - 0 := by linarith
    have h2 : (a + s - ε) / 2 - 0 ≤ 0 := by linarith
    rw [abs_le]
    constructor <;> linarith

end Riesz1
