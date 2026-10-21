/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.TransportScaled

/-!
# Fourier coefficients of a convolution with a periodic kernel

For an `L`-periodic kernel `K`, integrable over one period, and a function `f` integrable over
one period, the convolution `G(x) = ∫_0^L f(y) K(x - y) dy` satisfies, for every integer `k`,

`∫_0^L G(x) e_k(x) dx = (∫_0^L f(y) e_k(y) dy) (∫_0^L K(u) e_k(u) du)`,

where `e_k(x) = exp(-2πi k x / L)`. This is Fubini on one period together with the periodicity of
`K(u) e_k(u)`. It turns the transport identity on the circle into a statement about Fourier
coefficients.
-/

public section

open MeasureTheory Set intervalIntegral Filter Topology Complex
open scoped ContDiff Real

namespace Riesz1

/-- The normalized character `e_k(x) = exp(-2πi k x / L)`. -/
noncomputable def periodChar (L : ℝ) (k : ℤ) (x : ℝ) : ℂ :=
  Complex.exp (-(2 * π * I * (k : ℂ) * (x : ℂ) / (L : ℂ)))

lemma periodChar_add (L : ℝ) (k : ℤ) (x y : ℝ) :
    periodChar L k (x + y) = periodChar L k x * periodChar L k y := by
  unfold periodChar
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The character `e_k` is `L`-periodic. -/
lemma periodChar_at_period {L : ℝ} (hL : L ≠ 0) (k : ℤ) : periodChar L k L = 1 := by
  have hLc : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hL
  unfold periodChar
  rw [show 2 * π * I * (k : ℂ) * (L : ℂ) / (L : ℂ) = 2 * π * I * (k : ℂ) by field_simp]
  rw [show -(2 * π * I * (k : ℂ)) = ((-k : ℤ) : ℂ) * (2 * π * I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I _

/-- The character `e_k` is `L`-periodic. -/
lemma periodChar_periodic {L : ℝ} (hL : L ≠ 0) (k : ℤ) :
    Function.Periodic (periodChar L k) L := by
  intro x
  rw [periodChar_add, periodChar_at_period hL k, mul_one]

/-- The product `K(u) e_k(u)` is `L`-periodic whenever `K` is. -/
lemma periodic_kernel_char {L : ℝ} (hL : L ≠ 0) {K : ℝ → ℝ} (hK : Function.Periodic K L) (k : ℤ) :
    Function.Periodic (fun u => (K u : ℂ) * periodChar L k u) L := by
  intro u
  simp only [hK u, periodChar_periodic hL k u]

/-- The integral of a periodic function over a window is shift invariant. -/
lemma intervalIntegral_periodic_shift {L : ℝ} {g : ℝ → ℂ} (hg : Function.Periodic g L)
    (_hint : IntervalIntegrable g volume 0 L) (y : ℝ) :
    ∫ u in (0 : ℝ)..L, g (u + y) = ∫ u in (0 : ℝ)..L, g u := by
  have h := hg.intervalIntegral_add_eq y 0
  simp only [zero_add] at h
  rw [intervalIntegral.integral_comp_add_right g y, zero_add, add_comm L y]
  exact h

end Riesz1
