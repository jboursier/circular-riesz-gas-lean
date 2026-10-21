/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.FourierSmoothingGrid
public import Riesz1.ToMathlib.CircleSmoothDerivative
public import Riesz1.ToMathlib.CircleMollifyL2
public import Riesz1.Kernel.AdmissibilityRegularityDecay

/-!
# Derivative rates from normalized profile Fourier decay

Internal Fourier reconstruction for Lemma 5.1. The results in
`RegUniformDerivatives` discharge the coefficient hypotheses from the
admissibility predicates.
-/

public section

open MeasureTheory
open scoped ContDiff

namespace Riesz1.Internal

/-- Combine the low frequency integral norm and high frequency power bound.
The negative decay exponent permits a single bound at every nonzero mode. -/
theorem nonzero_coeff_power_bound {L g Z K : ℝ} (hL : 0 < L) (hg : g ≤ 0)
    {c : ℤ → ℂ} (hlo : ∀ k, L * ‖c k‖ ≤ Z)
    (hhi : ∀ k : ℤ, 1 ≤ |2 * Real.pi * (k : ℝ) / L| →
      L * ‖c k‖ ≤ K * |2 * Real.pi * (k : ℝ) / L| ^ g) :
    ∀ k : ℤ, k ≠ 0 → L * ‖c k‖ ≤
      ((|Z| + |K| + 1) * (2 * Real.pi) ^ g) * |(k : ℝ) / L| ^ g := by
  intro k hk
  have hu : 0 < |2 * Real.pi * (k : ℝ) / L| := by
    apply abs_pos.mpr
    exact div_ne_zero (mul_ne_zero (by positivity) (by exact_mod_cast hk)) hL.ne'
  have hb : L * ‖c k‖ ≤ (|Z| + |K| + 1) * |2 * Real.pi * (k : ℝ) / L| ^ g := by
    by_cases hw : 1 ≤ |2 * Real.pi * (k : ℝ) / L|
    · exact (hhi k hw).trans (mul_le_mul_of_nonneg_right
        (by linarith [le_abs_self K, abs_nonneg Z]) (by positivity))
    · have hw1 : 1 ≤ |2 * Real.pi * (k : ℝ) / L| ^ g :=
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu (le_of_not_ge hw) hg
      exact (hlo k).trans (by
        nlinarith [abs_nonneg K, abs_nonneg Z, le_abs_self Z,
          mul_le_mul_of_nonneg_left hw1 (by positivity : 0 ≤ |Z| + |K| + 1)])
  have he : |2 * Real.pi * (k : ℝ) / L| = (2 * Real.pi) * |(k : ℝ) / L| := by
    rw [mul_div_assoc, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  rw [he, Real.mul_rpow (by positivity) (abs_nonneg _), ← mul_assoc] at hb
  exact hb

/-- Actual circle smoothing has first and second classical derivative rates
when its normalized coefficients satisfy the indicated power estimate. -/
theorem circleMollify_derivative_rates {ρ : ℝ → ℝ} (hρ : IsMollifier ρ)
    {g K : ℝ} (hg : -2 < g) :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : Length)
      (f : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)}),
      (∀ k : ℤ, k ≠ 0 → L.val *
        ‖coeff L ⟨(fun x => (f.val x : ℂ)), complexL2Integrable L _ f.property⟩ k‖ ≤
          K * |(k : ℝ) / L.val| ^ g) →
      ∀ h : ℝ, 0 < h →
        ∃ fh : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)},
          Continuous fh.val ∧ ContDiff ℝ ∞ (fun x : ℝ => fh.val (x : Circle L)) ∧
          (∀ x : ℝ, fh.val (x : Circle L) = circleMollify ρ L.val h
            (fun t : ℝ => f.val (t : Circle L)) x) ∧
          (∀ x : ℝ, |deriv (fun t : ℝ => fh.val (t : Circle L)) x| ≤
            C * h ^ (-g - 2)) ∧
          ∀ x : ℝ, |deriv (deriv (fun t : ℝ => fh.val (t : Circle L))) x| ≤
            C * h ^ (-g - 3) := by
  obtain ⟨D₁, hD₁, hmoment₁⟩ := FourierGrid.smoothed_coeff_moment_bound hρ 1
    (K := K) (g := g) (by norm_num; linarith)
  obtain ⟨D₂, hD₂, hmoment₂⟩ := FourierGrid.smoothed_coeff_moment_bound hρ 2
    (K := K) (g := g) (by norm_num; linarith)
  let C := (2 * Real.pi) * D₁ + (2 * Real.pi) ^ 2 * D₂ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun L f hc h hh => ?_⟩
  have : Fact (0 < L.val) := ⟨L.property⟩
  obtain ⟨fh, hfc, hfs, hfv, hcoeff⟩ := exists_circleMollify_L2 hρ L hh f
  let c := fun k => coeff L ⟨(fun x => (f.val x : ℂ)), complexL2Integrable L _ f.property⟩ k
  have hm (m : ℕ) (hm0 : 0 < m) (D : ℝ)
      (hmoment : Summable (fun k : ℤ => if k = 0 then (0 : ℝ) else
        |(k : ℝ) / L.val| ^ m * ‖c k * (mollifierFT ρ (h * k / L.val) : ℂ)‖) ∧
      (∑' k : ℤ, if k = 0 then (0 : ℝ) else
        |(k : ℝ) / L.val| ^ m * ‖c k * (mollifierFT ρ (h * k / L.val) : ℂ)‖) ≤
          D * h ^ (-(m : ℝ) - g - 1)) :
      Summable (fun k : ℤ => ‖2 * Real.pi * Complex.I * (k : ℂ) / L.val‖ ^ m *
        ‖fourierCoeff (fun x => (fh.val x : ℂ)) k‖) ∧
      (∑' k : ℤ, ‖2 * Real.pi * Complex.I * (k : ℂ) / L.val‖ ^ m *
        ‖fourierCoeff (fun x => (fh.val x : ℂ)) k‖) ≤
          (2 * Real.pi) ^ m * D * h ^ (-(m : ℝ) - g - 1) := by
    have he (k : ℤ) : ‖2 * Real.pi * Complex.I * (k : ℂ) / L.val‖ ^ m *
        ‖fourierCoeff (fun x => (fh.val x : ℂ)) k‖ =
        (2 * Real.pi) ^ m * (if k = 0 then (0 : ℝ) else
          |(k : ℝ) / L.val| ^ m * ‖c k * (mollifierFT ρ (h * k / L.val) : ℂ)‖) := by
      change _ * ‖coeff L ⟨(fun x => (fh.val x : ℂ)), complexL2Integrable L _ fh.property⟩ k‖ = _
      rw [hcoeff, norm_circle_frequency]
      by_cases hk : k = 0
      · simp only [hk, Int.cast_zero, mul_zero, zero_div, abs_zero,
          zero_pow (Nat.ne_of_gt hm0), zero_mul, ite_true, mul_zero]
      · rw [ite_eq_right hk, show |2 * Real.pi * (k : ℝ) / L.val| =
            (2 * Real.pi) * |(k : ℝ) / L.val| by
              rw [mul_div_assoc, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)], mul_pow]
        dsimp only [c]
        ring
    simp_rw [he]
    refine ⟨hmoment.1.mul_left _, ?_⟩
    rw [tsum_mul_left]
    exact (mul_le_mul_of_nonneg_left hmoment.2 (by positivity)).trans_eq (by ring)
  have hfirst := hm 1 (by norm_num) D₁ (hmoment₁ L.val h L.property hh c hc)
  have hsecond := hm 2 (by norm_num) D₂ (hmoment₂ L.val h L.property hh c hc)
  norm_num only [pow_one, Nat.cast_one, Nat.cast_ofNat] at hfirst hsecond
  refine ⟨fh, hfc, hfs, hfv, fun x => ?_, fun x => ?_⟩
  · have hb := (CircleFourier.abs_deriv_le_fourier_moment hfc hfs hfirst.1 x).trans hfirst.2
    rw [show -(1 : ℝ) - g - 1 = -g - 2 by ring] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (by
      dsimp [C]
      nlinarith [show 0 ≤ (2 * Real.pi) * D₁ by positivity,
        show 0 ≤ (2 * Real.pi) ^ 2 * D₂ by positivity]) (by positivity))
  · have hb := (CircleFourier.abs_secondDeriv_le_fourier_moment hfc hfs hsecond.1 x).trans hsecond.2
    rw [show -(2 : ℝ) - g - 1 = -g - 3 by ring] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (by
      dsimp [C]
      nlinarith [show 0 ≤ (2 * Real.pi) * D₁ by positivity,
        show 0 ≤ (2 * Real.pi) ^ 2 * D₂ by positivity]) (by positivity))

end Riesz1.Internal
