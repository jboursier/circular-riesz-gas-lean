/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.CircleFourierDerivative

/-!
# The derivative Fourier identity on any fundamental interval

Translation of a fundamental interval preserves the Fourier integral of a periodic
derivative, including at points where the total derivative is defined to be zero.
-/

public section

open MeasureTheory Set

namespace Riesz1.CircleFourier

/-- The total derivative of a periodic real function is periodic. -/
theorem periodic_deriv {f : ℝ → ℝ} {T : ℝ} (hf : Function.Periodic f T) :
    Function.Periodic (deriv f) T := by
  have he : (fun t => f (t + T)) = f := funext hf
  intro t
  calc deriv f (t + T) = deriv (fun u => f (u + T)) t := (deriv_comp_add_const f T t).symm
    _ = deriv f t := by rw [he]

/-- The punctured-derivative Fourier formula holds on every fundamental interval. -/
theorem integral_deriv_mul_fourier_shift {T : ℝ} [Fact (0 < T)]
    {f : AddCircle T → ℝ} (hf : Continuous f) {S : Set ℝ} (hS : S.Countable)
    (hd : ∀ x : ℝ, x ∉ S → DifferentiableAt ℝ (fun t : ℝ => f (t : AddCircle T)) x)
    (hi : IntervalIntegrable (deriv (fun t : ℝ => f (t : AddCircle T))) volume 0 T)
    (a : ℝ) (k : ℤ) :
    (∫ t in a..a + T, ((deriv (fun u : ℝ => f (u : AddCircle T)) t : ℝ) : ℂ) *
        fourier (-k) (t : AddCircle T)) =
      (T : ℂ) * (2 * Real.pi * Complex.I * (k : ℂ) / T) *
        fourierCoeff (fun x => (f x : ℂ)) k := by
  have hp : Function.Periodic (fun t : ℝ => f (t : AddCircle T)) T := by
    intro t
    simp only [AddCircle.coe_add, AddCircle.coe_period, add_zero]
  have hper : Function.Periodic (fun t : ℝ =>
      ((deriv (fun u : ℝ => f (u : AddCircle T)) t : ℝ) : ℂ) *
        fourier (-k) (t : AddCircle T)) T := by
    intro t
    dsimp only
    rw [periodic_deriv hp t]
    simp only [AddCircle.coe_add, AddCircle.coe_period, add_zero]
  rw [hper.intervalIntegral_add_eq a 0, zero_add]
  exact integral_deriv_mul_fourier hf hS hd hi k

end Riesz1.CircleFourier
