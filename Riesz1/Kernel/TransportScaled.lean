/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.TransportIdentity

/-!
# The transport kernel on circles of arbitrary length

For `L > 0`, the kernel is `K_{s,L}(r) = L^{s-1} K_s(r/L)`. This file transfers the
unit-circle facts to `K_{s,L}`: `L`-periodicity, interval integrability, vanishing mean over a
period, the pointwise and `L¹` convergence of the symmetric sums
`∑_{|k| ≤ M} sgn(r - kL)|r - kL|^{s-1}`, all by the scaling `r = L u`.
-/

public section

open MeasureTheory Set intervalIntegral Filter Topology
open scoped ContDiff Real

namespace Riesz1

/-- The kernel `K_{s,L}(r) = L^{s-1} K_s(r/L)`. -/
noncomputable def scaledKernel (s L r : ℝ) : ℝ :=
  L ^ (s - 1) * periodicKernel s (r / L)

/-- The signed power is homogeneous: `sgn(Lu)|Lu|^{s-1} = L^{s-1} sgn(u)|u|^{s-1}` for `L > 0`. -/
lemma signPow_mul_pos {s L u : ℝ} (hL : 0 < L) : signPow s (L * u) = L ^ (s - 1) * signPow s u := by
  unfold signPow
  rcases lt_trichotomy u 0 with hu | hu | hu
  · rw [Real.sign_of_neg (mul_neg_of_pos_of_neg hL hu), Real.sign_of_neg hu, abs_mul,
      abs_of_pos hL, Real.mul_rpow hL.le (abs_nonneg u)]
    ring
  · simp [hu]
  · rw [Real.sign_of_pos (mul_pos hL hu), Real.sign_of_pos hu, abs_mul, abs_of_pos hL,
      Real.mul_rpow hL.le (abs_nonneg u)]
    ring

/-- The scaled kernel is `L`-periodic. -/
lemma scaledKernel_add_period {s L : ℝ} (hL : 0 < L) (r : ℝ) :
    scaledKernel s L (r + L) = scaledKernel s L r := by
  unfold scaledKernel
  congr 1
  rw [show (r + L) / L = r / L + 1 by field_simp]
  have h := periodicKernel_add_int s (r / L) 1
  rw [Int.cast_one] at h
  exact h

/-- The scaled symmetric sums: `∑_{|k| ≤ M} sgn(r - kL)|r - kL|^{s-1}`. -/
lemma signPow_scaled_sum {s L r : ℝ} (hL : 0 < L) (M : ℕ) :
    ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (r - k * L) =
      L ^ (s - 1) * ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (r / L - k) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← signPow_mul_pos hL]
  congr 1
  field_simp

/-- Pointwise convergence of the scaled symmetric sums off the lattice `L ℤ`. -/
lemma tendsto_scaled_signPow {s L r : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hL : 0 < L)
    (hr : ∀ k : ℤ, r ≠ k * L) :
    Tendsto (fun M : ℕ => ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (r - k * L)) atTop
      (𝓝 (scaledKernel s L r)) := by
  have hu : ∀ k : ℤ, r / L ≠ k := fun k h => hr k (by field_simp at h; linarith)
  have h := (tendsto_symmetric_signPow hs0 hs1 hu).const_mul (L ^ (s - 1))
  refine h.congr fun M => ?_
  rw [signPow_scaled_sum hL]

/-- `L¹` convergence of the scaled symmetric sums on `[-L/2, L/2]` (one period). -/
lemma tendsto_scaled_signPow_L1 {s L : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hL : 0 < L) :
    Tendsto (fun M : ℕ => ∫ r in (-(L / 2))..(L / 2),
      |∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (r - k * L) - scaledKernel s L r|)
      atTop (𝓝 0) := by
  have hunit := tendsto_symmetric_signPow_L1 hs0 hs1
  have key : ∀ M : ℕ, (∫ r in (-(L / 2))..(L / 2),
      |∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (r - k * L) - scaledKernel s L r|) =
      (L ^ (s - 1) * L) * ∫ t in (-(1 / 2 : ℝ))..(1 / 2),
        |∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (t - k) - periodicKernel s t| := by
    intro M
    have e : ∀ r : ℝ, |∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (r - k * L) -
        scaledKernel s L r| = L ^ (s - 1) *
        |∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (r / L - k) - periodicKernel s (r / L)| := by
      intro r
      rw [signPow_scaled_sum hL, scaledKernel, ← mul_sub, abs_mul,
        abs_of_pos (Real.rpow_pos_of_pos hL _)]
    rw [intervalIntegral.integral_congr (fun r _ => e r), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_div (fun t : ℝ =>
        |∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (t - k) - periodicKernel s t|) hL.ne']
    rw [show -(L / 2) / L = -(1 / 2 : ℝ) by field_simp, show L / 2 / L = (1 / 2 : ℝ) by field_simp,
      smul_eq_mul]
    ring
  have h := hunit.const_mul (L ^ (s - 1) * L)
  rw [mul_zero] at h
  exact h.congr fun M => (key M).symm

/-- The periodic kernel integrates to zero over the centred period `[-1/2, 1/2]`. -/
lemma integral_periodicKernel_half {s : ℝ} :
    ∫ t in (-(1 / 2 : ℝ))..(1 / 2), periodicKernel s t = 0 := by
  have h := (periodicKernel_periodic s).intervalIntegral_add_eq (-(1 / 2 : ℝ)) 0
  rw [show -(1 / 2 : ℝ) + 1 = 1 / 2 by ring, zero_add] at h
  rw [h]
  exact integral_periodicKernel s

/-- The scaled kernel has zero integral over one period `[-L/2, L/2]`. -/
lemma integral_scaledKernel_period {s L : ℝ} (hL : 0 < L) :
    ∫ r in (-(L / 2))..(L / 2), scaledKernel s L r = 0 := by
  unfold scaledKernel
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_div (fun t : ℝ => periodicKernel s t) hL.ne']
  rw [show -(L / 2) / L = -(1 / 2 : ℝ) by field_simp, show L / 2 / L = (1 / 2 : ℝ) by field_simp,
    integral_periodicKernel_half, smul_zero, mul_zero]

/-- The scaled kernel is interval integrable on every interval. -/
lemma intervalIntegrable_scaledKernel {s L : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hL : 0 < L)
    (a b : ℝ) : IntervalIntegrable (scaledKernel s L) volume a b := by
  have h := intervalIntegrable_periodicKernel_all hs0 hs1 (a * L⁻¹) (b * L⁻¹)
  have h1 := (h.comp_mul_left (c := L⁻¹)).const_mul (L ^ (s - 1))
  rw [show a * L⁻¹ / L⁻¹ = a by field_simp, show b * L⁻¹ / L⁻¹ = b by field_simp] at h1
  refine h1.congr_uIoo (fun r _ => ?_)
  unfold scaledKernel
  rw [show r / L = L⁻¹ * r by ring]

end Riesz1
