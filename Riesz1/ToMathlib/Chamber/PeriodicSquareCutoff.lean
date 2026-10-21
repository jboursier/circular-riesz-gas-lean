/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.Chamber.PeriodicCutoff
public import Riesz1.ToMathlib.Chamber.PeriodizationDerivative
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# A smooth square partition under integeperiodicSquareCutoff translations

The sine of the existing strip cutoff gives a compact smooth function
whose squared integeperiodicSquareCutoff translates sum to one. Differentiating this locally
finite identity supplies the cancellation needed in cutoff energy assembly.
-/

@[expose] public section

noncomputable section

open Set Function
open scoped ContDiff

namespace Riesz1

/-- A compact smooth rotation weight with a square partition of unity. -/
def periodicSquareCutoff (t : ℝ) : ℝ := Real.sin (Real.pi / 2 * periodicCutoff t)

theorem contDiff_periodicSquareCutoff : ContDiff ℝ ∞ periodicSquareCutoff :=
  Real.contDiff_sin.comp (contDiff_const.mul contDiff_periodicCutoff)

theorem periodicSquareCutoff_eq_zero {t : ℝ} (ht : t ≤ -1 ∨ 1 ≤ t) :
    periodicSquareCutoff t = 0 := by
  rw [periodicSquareCutoff, periodicCutoff_eq_zero ht, mul_zero, Real.sin_zero]

theorem hasCompactSupport_periodicSquareCutoff : HasCompactSupport periodicSquareCutoff :=
  hasCompactSupport_periodicCutoff.comp_left
    (g := fun t : ℝ => Real.sin (Real.pi / 2 * t)) (by rw [mul_zero, Real.sin_zero])

/-- The two nonzero translates are a sine and a cosine of the same angle. -/
theorem finsum_periodicSquareCutoff_sq (t : ℝ) :
    ∑ᶠ k : ℤ, periodicSquareCutoff (t + k) ^ 2 = 1 := by
  classical
  let m := ⌊t⌋
  let s : Finset ℤ := {-m - 1, -m}
  have h0 : (0 : ℝ) ≤ t - m := sub_nonneg.mpr (Int.floor_le t)
  have h1 : t - m < (1 : ℝ) := by
    have hh := Int.lt_floor_add_one t
    change t - (⌊t⌋ : ℝ) < 1
    linarith
  rw [finsum_eq_sum_of_support_subset _ (s := s) (by
    intro k hk
    by_contra hks
    have hne₁ : k ≠ -m - 1 := (not_or.mp (by simpa [s] using hks)).1
    have hne₂ : k ≠ -m := (not_or.mp (by simpa [s] using hks)).2
    have hk' : k ≤ -m - 2 ∨ -m + 1 ≤ k := by omega
    apply hk
    change periodicSquareCutoff (t + k) ^ 2 = 0
    rw [periodicSquareCutoff_eq_zero (by
      rcases hk' with hk' | hk'
      · left
        have : (k : ℝ) ≤ -m - 2 := by exact_mod_cast hk'
        linarith
      · right
        have : -(m : ℝ) + 1 ≤ k := by exact_mod_cast hk'
        linarith), zero_pow (by norm_num : (2 : ℕ) ≠ 0)])]
  have hmem : -m - 1 ∉ ({-m} : Finset ℤ) := by simp only [Finset.mem_singleton]; omega
  simp only [s, Finset.sum_insert hmem, Finset.sum_singleton,
    periodicSquareCutoff, periodicCutoff, Int.cast_sub, Int.cast_neg, Int.cast_one]
  rw [Real.smoothTransition.zero_of_nonpos (by linarith : t + (-↑m - 1) ≤ 0),
    Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ t + -↑m + 1)]
  rw [show t + (-↑m - 1) + 1 = t + -↑m by ring, sub_zero]
  rw [show Real.pi / 2 * (1 - Real.smoothTransition (t + -↑m)) =
    Real.pi / 2 - Real.pi / 2 * Real.smoothTransition (t + -↑m) by ring,
    Real.sin_pi_div_two_sub]
  exact Real.sin_sq_add_cos_sq _

/-- The sum of weight times derivative vanishes. This is obtained by
differentiating the square partition, ratheperiodicSquareCutoff than assuming seam cancellation. -/
theorem finsum_periodicSquareCutoff_mul_fderiv (t w : ℝ) :
    ∑ᶠ k : ℤ, periodicSquareCutoff (t + k) *
      fderiv ℝ periodicSquareCutoff (t + k) w = 0 := by
  have hs : HasCompactSupport (fun t => periodicSquareCutoff t ^ 2) :=
    hasCompactSupport_periodicSquareCutoff.comp_left
      (g := fun t : ℝ => t ^ 2) (zero_pow (by norm_num))
  have he : vectorPeriodize (1 : ℝ) one_ne_zero (fun t => periodicSquareCutoff t ^ 2) hs = fun _ => 1 := by
    funext x
    simpa only [vectorPeriodize, smul_eq_mul, mul_one ] using finsum_periodicSquareCutoff_sq x
  have hd := fderiv_vectorPeriodize_apply (v := (1 : ℝ)) one_ne_zero
    ((contDiff_periodicSquareCutoff.pow 2).differentiable (by norm_num)) hs t w
  rw [he, fderiv_const_apply] at hd
  have hp (x : ℝ) : fderiv ℝ (fun t => periodicSquareCutoff t ^ 2) x w =
      2 * (periodicSquareCutoff x * fderiv ℝ periodicSquareCutoff x w) := by
    rw [fderiv_fun_pow 2 (contDiff_periodicSquareCutoff.differentiable (by norm_num) x)]
    simp only [smul_apply, Nat.reduceSub, pow_one, nsmul_eq_mul, Nat.cast_ofNat, smul_eq_mul]
    ring
  simp only [vectorPeriodize, smul_eq_mul, mul_one, zero_apply, hp] at hd
  rw [← mul_finsum] at hd
  have hz : (2 : ℝ) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp hd.symm).resolve_left hz

end Riesz1
