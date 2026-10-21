/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.TransportKernelL1
public import Riesz1.Kernel.TransportFormula

/-!
# The transport as a convolution with the kernel

For a smooth real `ξ` on the unit circle, the kernel series of the pointwise transport formula
equals the convolution with `K_s`:

`∑_k ∫_0^1 (ξ(y) - ∫ξ) sgn(x-y-k)|x-y-k|^{s-1} dy = ∫_0^1 ξ(y) K_s(x-y) dy`.

The proof sums the symmetric partial sums, passes to the limit with the `L¹` convergence of the
symmetric sums on unit intervals (`tendsto_L1_unit_interval`), and removes the mean with the
vanishing integral of `K_s` over a period. This is the form in which the convolution formula
is used.
-/

public section

open MeasureTheory Set intervalIntegral Filter Topology
open scoped ContDiff Real

namespace Riesz1

/-- The periodic kernel integrates to zero over any unit window. -/
lemma integral_periodicKernel_sub_window {s : ℝ} (x : ℝ) :
    ∫ t in (0 : ℝ)..1, periodicKernel s (x - t) = 0 := by
  rw [intervalIntegral.integral_comp_sub_left (fun u => periodicKernel s u) x]
  rw [show x - 1 = x - 1 from rfl]
  have h := (periodicKernel_periodic s).intervalIntegral_add_eq (x - 1) 0
  rw [show x - 1 + 1 = x by ring] at h
  rw [show x - 0 = x by ring] at *
  rw [h]
  simpa using integral_periodicKernel s

/-- The kernel series of the transport equals the convolution with `K_s`. -/
theorem tsum_centered_eq_integral_kernel {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    {ξ : UnitAddCircle → ℝ} (hξ : IsSmoothCircle ξ) (x : ℝ) :
    ∑' k : ℤ, (∫ y in (0 : ℝ)..1, (ξ (y : UnitAddCircle) - circleMean ξ) * signPow s (x - y - k)) =
      ∫ y in (0 : ℝ)..1, ξ (y : UnitAddCircle) * periodicKernel s (x - y) := by
  set ξ' : ℝ → ℝ := fun t => ξ (t : UnitAddCircle) - circleMean ξ with hξ'
  have hξc : Continuous ξ' := continuous_centered hξ
  obtain ⟨M0, hM0⟩ := exists_bound_centered hξ
  have hmean : ∫ t in (0 : ℝ)..1, ξ' t = 0 := integral_centered_eq_zero hξ
  have hsum : Summable fun k : ℤ => ∫ t in (0 : ℝ)..1, ξ' t * signPow s (x - t - k) :=
    summable_centered_signPow hs0 hs1 hξc hM0 hmean
  -- The partial sums are integrals of the symmetric sums.
  have hpart : ∀ M : ℕ, ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), ∫ t in (0 : ℝ)..1,
      ξ' t * signPow s (x - t - k) =
      ∫ t in (0 : ℝ)..1, ξ' t * ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s ((x - t) - k) := by
    intro M
    rw [← intervalIntegral.integral_finsetSum]
    · refine intervalIntegral.integral_congr fun t _ => ?_
      simp only [Finset.mul_sum]
    · intro k _
      exact intervalIntegrable_centered_signPow hs0 hs1 hξc hM0 k
  -- The `L¹` deviation of the partial sums on the window `[0, 1]` (after `t ↦ x - t`).
  have hwin : ∀ M : ℕ, ∫ t in (0 : ℝ)..1, |∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
      signPow s ((x - t) - k) - periodicKernel s (x - t)| =
      ∫ u in (x - 1)..x, |∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (u - k) -
        periodicKernel s u| := by
    intro M
    have := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := 1)
      (fun u : ℝ => |∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s (u - k) -
        periodicKernel s u|) x
    simpa [sub_zero] using this
  have hL1 : Tendsto (fun M : ℕ => ∫ t in (0 : ℝ)..1, |∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
      signPow s ((x - t) - k) - periodicKernel s (x - t)|) atTop (𝓝 0) := by
    simp_rw [hwin]
    have h := tendsto_L1_unit_interval hs0 hs1 (x - 1)
    rw [show x - 1 + 1 = x by ring] at h
    exact h
  -- The convergence of the partial sums to the convolution, with the constant `M0`.
  have hbd : ∀ M : ℕ, |(∫ t in (0 : ℝ)..1, ξ' t * ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        signPow s ((x - t) - k)) - ∫ t in (0 : ℝ)..1, ξ' t * periodicKernel s (x - t)| ≤
      M0 * ∫ t in (0 : ℝ)..1, |∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        signPow s ((x - t) - k) - periodicKernel s (x - t)| := by
    intro M
    -- integrability of the difference `D(x - t)` on `[0, 1]`
    have hD : IntervalIntegrable (fun t : ℝ => ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        signPow s ((x - t) - k) - periodicKernel s (x - t)) volume 0 1 := by
      have h := (intervalIntegrable_symmetricSum_sub hs0 hs1 M (x - 1) x).comp_sub_left x
      rw [show x - (x - 1) = 1 by ring, show x - x = 0 by ring] at h
      exact h.symm
    have hpD : IntervalIntegrable (fun t : ℝ => ξ' t * (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        signPow s ((x - t) - k) - periodicKernel s (x - t))) volume 0 1 := by
      have h : IntervalIntegrable (fun t : ℝ => (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
          signPow s ((x - t) - k) - periodicKernel s (x - t)) * ξ' t) volume 0 1 :=
        hD.mul_continuousOn hξc.continuousOn
      exact IntervalIntegrable.congr_uIoo h (fun t _ => mul_comm _ _)
    have hK : IntervalIntegrable (fun t : ℝ => ξ' t * periodicKernel s (x - t)) volume 0 1 := by
      have h0 := (intervalIntegrable_periodicKernel_all hs0 hs1 (x - 1) x).comp_sub_left x
      rw [show x - (x - 1) = 1 by ring, show x - x = 0 by ring] at h0
      have h : IntervalIntegrable (fun t : ℝ => periodicKernel s (x - t) * ξ' t) volume 0 1 :=
        h0.symm.mul_continuousOn hξc.continuousOn
      exact IntervalIntegrable.congr_uIoo h (fun t _ => mul_comm _ _)
    have hS : IntervalIntegrable (fun t : ℝ => ξ' t * ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        signPow s ((x - t) - k)) volume 0 1 := by
      have h : IntervalIntegrable (fun t : ℝ => ξ' t * (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
          signPow s ((x - t) - k) - periodicKernel s (x - t)) + ξ' t * periodicKernel s (x - t))
          volume 0 1 := hpD.add hK
      refine IntervalIntegrable.congr_uIoo h (fun t _ => ?_)
      ring
    have e : (∫ t in (0 : ℝ)..1, ξ' t * ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        signPow s ((x - t) - k)) - ∫ t in (0 : ℝ)..1, ξ' t * periodicKernel s (x - t) =
        ∫ t in (0 : ℝ)..1, ξ' t * (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
          signPow s ((x - t) - k) - periodicKernel s (x - t)) := by
      rw [← intervalIntegral.integral_sub hS hK]
      refine intervalIntegral.integral_congr fun t _ => ?_
      ring
    rw [e]
    calc |∫ t in (0 : ℝ)..1, ξ' t * (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
          signPow s ((x - t) - k) - periodicKernel s (x - t))|
        = ‖∫ t in (0 : ℝ)..1, ξ' t * (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
          signPow s ((x - t) - k) - periodicKernel s (x - t))‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ t in (0 : ℝ)..1, ‖ξ' t * (∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
          signPow s ((x - t) - k) - periodicKernel s (x - t))‖ :=
          intervalIntegral.norm_integral_le_integral_norm zero_le_one
      _ ≤ ∫ t in (0 : ℝ)..1, M0 * ‖∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
          signPow s ((x - t) - k) - periodicKernel s (x - t)‖ := by
          refine intervalIntegral.integral_mono_on zero_le_one hpD.norm (hD.norm.const_mul M0)
            (fun t _ => ?_)
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (by rw [Real.norm_eq_abs]; exact hM0 t) (norm_nonneg _)
      _ = M0 * ∫ t in (0 : ℝ)..1, |∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
          signPow s ((x - t) - k) - periodicKernel s (x - t)| := by
          rw [intervalIntegral.integral_const_mul]
          simp only [Real.norm_eq_abs]
  have hlim : Tendsto (fun M : ℕ => ∫ t in (0 : ℝ)..1, ξ' t *
      ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), signPow s ((x - t) - k))
      atTop (𝓝 (∫ t in (0 : ℝ)..1, ξ' t * periodicKernel s (x - t))) := by
    have h2 := hL1.const_mul M0
    rw [mul_zero] at h2
    refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
    refine squeeze_zero (fun M => norm_nonneg _) (fun M => ?_) h2
    simpa [Real.norm_eq_abs] using hbd M
  -- The series is the limit of its partial sums, which are the integrals above.
  have hsum_eq : ∑' k : ℤ, ∫ t in (0 : ℝ)..1, ξ' t * signPow s (x - t - k) =
      ∫ t in (0 : ℝ)..1, ξ' t * periodicKernel s (x - t) := by
    have h1 := tendsto_symmetric_sum hsum
    have h2 : Tendsto (fun M : ℕ => ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        ∫ t in (0 : ℝ)..1, ξ' t * signPow s (x - t - k)) atTop
        (𝓝 (∫ t in (0 : ℝ)..1, ξ' t * periodicKernel s (x - t))) :=
      hlim.congr (fun M => (hpart M).symm)
    exact tendsto_nhds_unique h1 h2
  -- The mean of `ξ` is removed, since the kernel has zero integral over a window.
  have h0 := (intervalIntegrable_periodicKernel_all hs0 hs1 (x - 1) x).comp_sub_left x
  rw [show x - (x - 1) = 1 by ring, show x - x = 0 by ring] at h0
  have hKw : IntervalIntegrable (fun t : ℝ => periodicKernel s (x - t)) volume 0 1 := h0.symm
  have hξK : IntervalIntegrable (fun t : ℝ => ξ (t : UnitAddCircle) * periodicKernel s (x - t))
      volume 0 1 := by
    have h : IntervalIntegrable (fun t : ℝ => periodicKernel s (x - t) * ξ (t : UnitAddCircle))
        volume 0 1 :=
      hKw.mul_continuousOn (continuous_lift hξ).continuousOn
    exact IntervalIntegrable.congr_uIoo h (fun t _ => mul_comm _ _)
  have hK : IntervalIntegrable (fun t : ℝ => ξ' t * periodicKernel s (x - t)) volume 0 1 := by
    have h : IntervalIntegrable (fun t : ℝ => periodicKernel s (x - t) * ξ' t) volume 0 1 :=
      hKw.mul_continuousOn hξc.continuousOn
    exact IntervalIntegrable.congr_uIoo h (fun t _ => mul_comm _ _)
  have hmK : IntervalIntegrable (fun t : ℝ => circleMean ξ * periodicKernel s (x - t)) volume 0 1 :=
    hKw.const_mul _
  have hsplit : ∫ t in (0 : ℝ)..1, ξ (t : UnitAddCircle) * periodicKernel s (x - t) =
      ∫ t in (0 : ℝ)..1, ξ' t * periodicKernel s (x - t) := by
    have e : ∀ t : ℝ, ξ (t : UnitAddCircle) * periodicKernel s (x - t) =
        ξ' t * periodicKernel s (x - t) + circleMean ξ * periodicKernel s (x - t) := fun t => by
      simp only [hξ']
      ring
    rw [intervalIntegral.integral_congr (fun t _ => e t), intervalIntegral.integral_add hK hmK,
      intervalIntegral.integral_const_mul, integral_periodicKernel_sub_window, mul_zero, add_zero]
  rw [hsplit]
  exact hsum_eq

end Riesz1
