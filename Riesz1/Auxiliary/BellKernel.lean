/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Auxiliary.BellIncrement
public import Riesz1.Auxiliary.GradientSplittingKernel

/-!
# Bounds for the averaged kernel

The averaged kernel `q` and the kernel part of Lemma B.1.
The kernel is
`q(y) = N^{-s} ℓ² g''(y/N) D(y/N)` for `0 < y < N`, where `g` is the periodic Riesz kernel
`hurwitzKernel s` and `D` is `bellIncrement` of `BellIncrement.lean`.

The proof uses the derivative bounds of `gradient_splitting_kernel` for `g''` and `g'''` on
`0 < |r| ≤ 3/4`, the bounds of `BellIncrement.lean` for `D` and `D'`, and the reflection
`q(N - y) = q(y)`.
-/

@[expose] public section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace Riesz1

/-- The averaged kernel `q(y) = N^{-s} ℓ² g''(y/N) D(y/N)`, where `g` is
the periodic Riesz kernel `hurwitzKernel s`. The paper defines `q` on `0 < y < N`. This is
the formula there, and every statement below restricts to `Ioo 0 N`. -/
noncomputable def bellKernel (s : ℝ) (N : ℕ) (ℓ : ℝ) (ψ : ℝ → ℝ) (y : ℝ) : ℝ :=
  (N : ℝ) ^ (-s) * ℓ ^ 2 * iteratedDeriv 2 (hurwitzKernel s) (y / N) * bellIncrement ℓ ψ (y / N)

/-- The derivative of `bellKernel`, written out by the product and chain rules. -/
noncomputable def bellKernelDeriv (s : ℝ) (N : ℕ) (ℓ : ℝ) (ψ : ℝ → ℝ) (y : ℝ) : ℝ :=
  (N : ℝ) ^ (-s) * ℓ ^ 2 *
    (iteratedDeriv 3 (hurwitzKernel s) (y / N) * (1 / N) * bellIncrement ℓ ψ (y / N) +
      iteratedDeriv 2 (hurwitzKernel s) (y / N) * (bellIncrementDeriv ℓ ψ (y / N) * (1 / N)))

/-- The second derivative of the kernel is one-periodic. -/
lemma iteratedDeriv_two_periodic (s t : ℝ) :
    iteratedDeriv 2 (hurwitzKernel s) (t + 1) = iteratedDeriv 2 (hurwitzKernel s) t := by
  have hfun : (fun z => hurwitzKernel s (z + 1)) = hurwitzKernel s :=
    funext (hurwitzKernel_periodic s)
  have h := iteratedDeriv_comp_add_const 2 (hurwitzKernel s) 1
  rw [hfun] at h
  exact (congrFun h t).symm

/-- The second derivative of the even kernel is even. -/
lemma iteratedDeriv_two_neg (s r : ℝ) :
    iteratedDeriv 2 (hurwitzKernel s) (-r) = iteratedDeriv 2 (hurwitzKernel s) r := by
  rw [gradSplit_iteratedDeriv_kernel_neg]
  norm_num

/-- The averaged increment is nonnegative, as an integral of squares. -/
lemma bellIncrement_nonneg (ℓ : ℝ) (ψ : ℝ → ℝ) (r : ℝ) : 0 ≤ bellIncrement ℓ ψ r :=
  intervalIntegral.integral_nonneg zero_le_one (fun _ _ => sq_nonneg _)

/-- The energy `‖ψ'‖²_{L²(ℓ⁻¹𝕋)}` is nonnegative. -/
lemma bellEnergy_nonneg {ℓ : ℝ} {ψ : ℝ → ℝ} (hℓ : 0 < ℓ) : 0 ≤ bellEnergy ℓ ψ :=
  intervalIntegral.integral_nonneg (inv_nonneg.mpr hℓ.le) (fun _ _ => sq_nonneg _)

/-- The reflection `q(N - y) = q(y)`, from the evenness and periodicity of `D` and `g''`. -/
lemma bellKernel_reflect (s : ℝ) (N : ℕ) (hN : 0 < N) (ℓ : ℝ) (ψ : ℝ → ℝ)
    (hper : Function.Periodic ψ ℓ⁻¹) (y : ℝ) :
    bellKernel s N ℓ ψ ((N : ℝ) - y) = bellKernel s N ℓ ψ y := by
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have e : ((N : ℝ) - y) / N = -(y / N) + 1 := by
    rw [sub_div, div_self hN0]
    ring
  unfold bellKernel
  rw [e, iteratedDeriv_two_periodic s (-(y / N)), iteratedDeriv_two_neg s (y / N),
    bellIncrement_periodic hper (-(y / N)), bellIncrement_neg hper (y / N)]

/-- The derivative of the averaged kernel, at every point of `(0, N)`. -/
lemma hasDerivAt_bellKernel {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {N : ℕ} (hN : 0 < N)
    {ℓ : ℝ} {ψ : ℝ → ℝ} (hℓ : 0 < ℓ) (hψ : ContDiff ℝ ∞ ψ) {y : ℝ}
    (hy : y ∈ Ioo 0 (N : ℝ)) :
    HasDerivAt (bellKernel s N ℓ ψ) (bellKernelDeriv s N ℓ ψ y) y := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  obtain ⟨hy0, hyN⟩ := hy
  have ht0 : 0 < y / N := div_pos hy0 hNpos
  have ht1 : y / N < 1 := (div_lt_one hNpos).mpr hyN
  have hne : ((y / N : ℝ) : UnitAddCircle) ≠ 0 :=
    gradSplit_coe_ne_zero (by rw [abs_of_pos ht0]; exact ht0) (by rw [abs_of_pos ht0]; exact ht1)
  have hG : HasDerivAt (iteratedDeriv 2 (hurwitzKernel s)) (iteratedDeriv 3 (hurwitzKernel s) (y / N))
      (y / N) :=
    gradSplit_hasDerivAt_iteratedDeriv s hs0 hs1 2 hne
  have hdiv : HasDerivAt (fun y : ℝ => y / (N : ℝ)) (1 / (N : ℝ)) y :=
    (hasDerivAt_id' y).div_const _
  have h1 : HasDerivAt (iteratedDeriv 2 (hurwitzKernel s) ∘ fun y : ℝ => y / (N : ℝ))
      (iteratedDeriv 3 (hurwitzKernel s) (y / N) * (1 / N)) y :=
    HasDerivAt.comp y hG hdiv
  have h2 : HasDerivAt (bellIncrement ℓ ψ ∘ fun y : ℝ => y / (N : ℝ))
      (bellIncrementDeriv ℓ ψ (y / N) * (1 / N)) y :=
    HasDerivAt.comp y (hasDerivAt_bellIncrement hℓ hψ (y / N)) hdiv
  have h4 := (h1.const_mul ((N : ℝ) ^ (-s) * ℓ ^ 2)).mul h2
  refine h4.congr_deriv ?_
  simp only [Function.comp_apply]
  unfold bellKernelDeriv
  ring

/-- The derivative of the averaged kernel is continuous on `(0, N)`. -/
lemma continuousOn_bellKernelDeriv {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {N : ℕ} (hN : 0 < N)
    {ℓ : ℝ} {ψ : ℝ → ℝ} (hℓ : 0 < ℓ) (hψ : ContDiff ℝ ∞ ψ) :
    ContinuousOn (bellKernelDeriv s N ℓ ψ) (Ioo 0 (N : ℝ)) := by
  intro y hy
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  obtain ⟨hy0, hyN⟩ := hy
  have ht0 : 0 < y / N := div_pos hy0 hNpos
  have ht1 : y / N < 1 := (div_lt_one hNpos).mpr hyN
  have hne : ((y / N : ℝ) : UnitAddCircle) ≠ 0 :=
    gradSplit_coe_ne_zero (by rw [abs_of_pos ht0]; exact ht0) (by rw [abs_of_pos ht0]; exact ht1)
  have hdiv : ContinuousAt (fun y : ℝ => y / (N : ℝ)) y :=
    (continuous_id.div_const _).continuousAt
  have hA : ContinuousAt (iteratedDeriv 3 (hurwitzKernel s) ∘ fun y : ℝ => y / (N : ℝ)) y :=
    ContinuousAt.comp (f := fun y : ℝ => y / (N : ℝ))
      (((gradSplit_hasDerivAt_iteratedDeriv s hs0 hs1 3 hne).continuousAt)) hdiv
  have hC : ContinuousAt (iteratedDeriv 2 (hurwitzKernel s) ∘ fun y : ℝ => y / (N : ℝ)) y :=
    ContinuousAt.comp (f := fun y : ℝ => y / (N : ℝ))
      (((gradSplit_hasDerivAt_iteratedDeriv s hs0 hs1 2 hne).continuousAt)) hdiv
  have hB : ContinuousAt (bellIncrement ℓ ψ ∘ fun y : ℝ => y / (N : ℝ)) y :=
    ContinuousAt.comp (f := fun y : ℝ => y / (N : ℝ))
      (continuous_bellIncrement hℓ hψ).continuousAt hdiv
  have hD : ContinuousAt (bellIncrementDeriv ℓ ψ ∘ fun y : ℝ => y / (N : ℝ)) y :=
    ContinuousAt.comp (f := fun y : ℝ => y / (N : ℝ))
      (continuous_bellIncrementDeriv hψ).continuousAt hdiv
  have hfin : ContinuousAt (bellKernelDeriv s N ℓ ψ) y := by
    unfold bellKernelDeriv
    exact continuousAt_const.mul
      (((hA.mul continuousAt_const).mul hB).add (hC.mul (hD.mul continuousAt_const)))
  exact hfin.continuousWithinAt

/-- The constant identity `ℓ² (ℓ⁻¹ ‖ψ'‖²) = A`. -/
lemma sq_mul_inv_mul_energy {ℓ : ℝ} {ψ : ℝ → ℝ} (hℓ : 0 < ℓ) :
    ℓ ^ 2 * (ℓ⁻¹ * bellEnergy ℓ ψ) = bellConstant ℓ ψ := by
  unfold bellConstant
  rw [show ℓ ^ 2 * (ℓ⁻¹ * bellEnergy ℓ ψ) = ℓ * (ℓ * ℓ⁻¹) * bellEnergy ℓ ψ by ring,
    mul_inv_cancel₀ hℓ.ne', mul_one]

/-- The power identity `t^(-s-2) t² = t^(-s)`. -/
lemma rpow_mul_sq_two {t : ℝ} (ht : 0 < t) (s : ℝ) : t ^ (-s - 2) * t ^ 2 = t ^ (-s) := by
  rw [← Real.rpow_natCast, ← Real.rpow_add ht]
  congr 1
  push_cast
  ring

/-- The power identity `t^(-s-3) t² = t^(-s-1)`. -/
lemma rpow_mul_sq_three {t : ℝ} (ht : 0 < t) (s : ℝ) :
    t ^ (-s - 3) * t ^ 2 = t ^ (-s - 1) := by
  rw [← Real.rpow_natCast, ← Real.rpow_add ht]
  congr 1
  push_cast
  ring

/-- The power identity `t^(-s-2) t = t^(-s-1)`. -/
lemma rpow_mul_self_two {t : ℝ} (ht : 0 < t) (s : ℝ) : t ^ (-s - 2) * t = t ^ (-s - 1) := by
  have h := Real.rpow_add ht (-s - 2) 1
  rw [Real.rpow_one] at h
  rw [← h]
  congr 1
  ring

/-- The scaling identity `N^{-s} (y/N)^{-s} = y^{-s}`. -/
lemma rpow_scale_neg {N y : ℝ} (hN : 0 < N) (hy : 0 < y) (s : ℝ) :
    N ^ (-s) * (y / N) ^ (-s) = y ^ (-s) := by
  rw [Real.div_rpow hy.le hN.le]
  have hNs : N ^ (-s) ≠ 0 := (Real.rpow_pos_of_pos hN _).ne'
  field_simp

/-- The scaling identity `N^{-s} N^{-1} (y/N)^{-s-1} = y^{-s-1}`. -/
lemma rpow_scale_neg_one {N y : ℝ} (hN : 0 < N) (hy : 0 < y) (s : ℝ) :
    N ^ (-s) * (1 / N) * (y / N) ^ (-s - 1) = y ^ (-s - 1) := by
  have hN1 : N ^ (-s - 1) = N ^ (-s) * (1 / N) := by
    rw [Real.rpow_sub hN, Real.rpow_one]
    ring
  rw [Real.div_rpow hy.le hN.le, ← hN1]
  have hNs : N ^ (-s - 1) ≠ 0 := (Real.rpow_pos_of_pos hN _).ne'
  field_simp

/-- The kernel part of Lemma B.1 on the left half: for `0 < y ≤ N/2`, the kernel and its
derivative satisfy the bounds with constant `C0` and `3 C0`. -/
lemma bellKernel_half_bounds {s : ℝ} {C0 : ℝ} (hC0 : 0 < C0)
    (hG2 : ∀ t : ℝ, 0 < t → t ≤ 3 / 4 → |iteratedDeriv 2 (hurwitzKernel s) t| ≤ C0 * t ^ (-s - 2))
    (hG3 : ∀ t : ℝ, 0 < t → t ≤ 3 / 4 → |iteratedDeriv 3 (hurwitzKernel s) t| ≤ C0 * t ^ (-s - 3))
    {N : ℕ} (hN : 0 < N) {ℓ : ℝ} {ψ : ℝ → ℝ} (hℓ : 0 < ℓ) (hψ : ContDiff ℝ ∞ ψ)
    (hper : Function.Periodic ψ ℓ⁻¹) {y : ℝ} (hy0 : 0 < y) (hyh : y ≤ (N : ℝ) / 2) :
    |bellKernel s N ℓ ψ y| ≤ C0 * bellConstant ℓ ψ * y ^ (-s) ∧
      |bellKernelDeriv s N ℓ ψ y| ≤ 3 * C0 * bellConstant ℓ ψ * y ^ (-s - 1) := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have ht0 : 0 < y / N := div_pos hy0 hNpos
  have ht1 : y / N ≤ 3 / 4 := by
    have h : y / N ≤ 1 / 2 := by
      rw [div_le_iff₀ hNpos]
      linarith
    linarith
  have hw0 : 0 ≤ 1 / (N : ℝ) := by positivity
  have hK0 : 0 ≤ (N : ℝ) ^ (-s) * ℓ ^ 2 :=
    mul_nonneg (Real.rpow_nonneg hNpos.le _) (sq_nonneg ℓ)
  have hD0 : 0 ≤ bellIncrement ℓ ψ (y / N) := bellIncrement_nonneg ℓ ψ _
  have hDle : bellIncrement ℓ ψ (y / N) ≤ (y / N) ^ 2 * (ℓ⁻¹ * bellEnergy ℓ ψ) :=
    (bellIncrement_le hℓ hψ hper (y / N)).trans (le_of_eq (by ring))
  have hD1 : |bellIncrementDeriv ℓ ψ (y / N)| ≤ 2 * (y / N) * (ℓ⁻¹ * bellEnergy ℓ ψ) := by
    have h := abs_bellIncrementDeriv_le hℓ hψ hper (y / N)
    rw [abs_of_pos ht0] at h
    exact h.trans (le_of_eq (by ring))
  unfold bellKernel bellKernelDeriv
  set t : ℝ := y / N with ht_def
  have hA : ℓ ^ 2 * (ℓ⁻¹ * bellEnergy ℓ ψ) = bellConstant ℓ ψ := sq_mul_inv_mul_energy hℓ
  have hsc : (N : ℝ) ^ (-s) * t ^ (-s) = y ^ (-s) := rpow_scale_neg hNpos hy0 s
  have hsc1 : (N : ℝ) ^ (-s) * (1 / N) * t ^ (-s - 1) = y ^ (-s - 1) :=
    rpow_scale_neg_one hNpos hy0 s
  have h_a : t ^ (-s - 2) * t ^ 2 = t ^ (-s) := rpow_mul_sq_two ht0 s
  have h_b : t ^ (-s - 3) * t ^ 2 = t ^ (-s - 1) := rpow_mul_sq_three ht0 s
  have h_c : t ^ (-s - 2) * t = t ^ (-s - 1) := rpow_mul_self_two ht0 s
  constructor
  · calc |(N : ℝ) ^ (-s) * ℓ ^ 2 * iteratedDeriv 2 (hurwitzKernel s) t * bellIncrement ℓ ψ t|
        = ((N : ℝ) ^ (-s) * ℓ ^ 2) * (|iteratedDeriv 2 (hurwitzKernel s) t| * bellIncrement ℓ ψ t) := by
          rw [abs_mul, abs_mul, abs_of_nonneg hK0, abs_of_nonneg hD0]
          ring
      _ ≤ ((N : ℝ) ^ (-s) * ℓ ^ 2) *
            ((C0 * t ^ (-s - 2)) * (t ^ 2 * (ℓ⁻¹ * bellEnergy ℓ ψ))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul (hG2 t ht0 ht1) hDle hD0 (mul_nonneg hC0.le (Real.rpow_nonneg ht0.le _)))
            hK0
      _ = C0 * bellConstant ℓ ψ * y ^ (-s) := by
          have e : ((N : ℝ) ^ (-s) * ℓ ^ 2) *
              ((C0 * t ^ (-s - 2)) * (t ^ 2 * (ℓ⁻¹ * bellEnergy ℓ ψ)))
              = C0 * (ℓ ^ 2 * (ℓ⁻¹ * bellEnergy ℓ ψ)) *
                  ((N : ℝ) ^ (-s) * (t ^ (-s - 2) * t ^ 2)) := by
            ring
          rw [e, h_a, hA, hsc]
  · have hX : |iteratedDeriv 3 (hurwitzKernel s) t * (1 / N) * bellIncrement ℓ ψ t|
        ≤ (C0 * t ^ (-s - 3)) * (1 / N) * (t ^ 2 * (ℓ⁻¹ * bellEnergy ℓ ψ)) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hw0, abs_of_nonneg hD0]
      exact mul_le_mul (mul_le_mul_of_nonneg_right (hG3 t ht0 ht1) hw0) hDle hD0
        (mul_nonneg (mul_nonneg hC0.le (Real.rpow_nonneg ht0.le _)) hw0)
    have hY : |iteratedDeriv 2 (hurwitzKernel s) t * (bellIncrementDeriv ℓ ψ t * (1 / N))|
        ≤ (C0 * t ^ (-s - 2)) * ((2 * t * (ℓ⁻¹ * bellEnergy ℓ ψ)) * (1 / N)) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hw0]
      exact mul_le_mul (hG2 t ht0 ht1) (mul_le_mul_of_nonneg_right hD1 hw0)
        (mul_nonneg (abs_nonneg _) hw0) (mul_nonneg hC0.le (Real.rpow_nonneg ht0.le _))
    calc |(N : ℝ) ^ (-s) * ℓ ^ 2 * (iteratedDeriv 3 (hurwitzKernel s) t * (1 / N) * bellIncrement ℓ ψ t +
          iteratedDeriv 2 (hurwitzKernel s) t * (bellIncrementDeriv ℓ ψ t * (1 / N)))|
        = ((N : ℝ) ^ (-s) * ℓ ^ 2) *
          |iteratedDeriv 3 (hurwitzKernel s) t * (1 / N) * bellIncrement ℓ ψ t +
            iteratedDeriv 2 (hurwitzKernel s) t * (bellIncrementDeriv ℓ ψ t * (1 / N))| := by
          rw [abs_mul, abs_of_nonneg hK0]
      _ ≤ ((N : ℝ) ^ (-s) * ℓ ^ 2) *
          (|iteratedDeriv 3 (hurwitzKernel s) t * (1 / N) * bellIncrement ℓ ψ t| +
            |iteratedDeriv 2 (hurwitzKernel s) t * (bellIncrementDeriv ℓ ψ t * (1 / N))|) :=
          mul_le_mul_of_nonneg_left (abs_add_le _ _) hK0
      _ ≤ ((N : ℝ) ^ (-s) * ℓ ^ 2) *
          ((C0 * t ^ (-s - 3)) * (1 / N) * (t ^ 2 * (ℓ⁻¹ * bellEnergy ℓ ψ)) +
            (C0 * t ^ (-s - 2)) * ((2 * t * (ℓ⁻¹ * bellEnergy ℓ ψ)) * (1 / N))) :=
          mul_le_mul_of_nonneg_left (add_le_add hX hY) hK0
      _ = 3 * C0 * bellConstant ℓ ψ * y ^ (-s - 1) := by
          have e : ((N : ℝ) ^ (-s) * ℓ ^ 2) *
              ((C0 * t ^ (-s - 3)) * (1 / N) * (t ^ 2 * (ℓ⁻¹ * bellEnergy ℓ ψ)) +
                (C0 * t ^ (-s - 2)) * ((2 * t * (ℓ⁻¹ * bellEnergy ℓ ψ)) * (1 / N)))
              = C0 * (ℓ ^ 2 * (ℓ⁻¹ * bellEnergy ℓ ψ)) * ((N : ℝ) ^ (-s) * (1 / N)) *
                  (t ^ (-s - 3) * t ^ 2 + 2 * (t ^ (-s - 2) * t)) := by
            ring
          have e2 : C0 * (ℓ ^ 2 * (ℓ⁻¹ * bellEnergy ℓ ψ)) * ((N : ℝ) ^ (-s) * (1 / N)) *
                (t ^ (-s - 3) * t ^ 2 + 2 * (t ^ (-s - 2) * t))
              = 3 * C0 * (ℓ ^ 2 * (ℓ⁻¹ * bellEnergy ℓ ψ)) *
                  ((N : ℝ) ^ (-s) * (1 / N) * t ^ (-s - 1)) := by
            rw [h_b, h_c]
            ring
          rw [e, e2, hA, hsc1]

/-- The kernel part of Lemma B.1 on `(0, N)`: the bounds for `q` and `q'` with constant `3 C0`. -/
lemma bellKernel_bounds {s : ℝ} {C0 : ℝ} (hC0 : 0 < C0)
    (hG2 : ∀ t : ℝ, 0 < t → t ≤ 3 / 4 → |iteratedDeriv 2 (hurwitzKernel s) t| ≤ C0 * t ^ (-s - 2))
    (hG3 : ∀ t : ℝ, 0 < t → t ≤ 3 / 4 → |iteratedDeriv 3 (hurwitzKernel s) t| ≤ C0 * t ^ (-s - 3))
    {N : ℕ} (hN : 0 < N) {ℓ : ℝ} {ψ : ℝ → ℝ} (hℓ : 0 < ℓ) (hψ : ContDiff ℝ ∞ ψ)
    (hper : Function.Periodic ψ ℓ⁻¹) (hs0 : 0 < s) (hs1 : s < 1) {y : ℝ}
    (hy : y ∈ Ioo 0 (N : ℝ)) :
    |bellKernel s N ℓ ψ y| ≤ 3 * C0 * bellConstant ℓ ψ * min y ((N : ℝ) - y) ^ (-s) ∧
      |deriv (bellKernel s N ℓ ψ) y|
        ≤ 3 * C0 * bellConstant ℓ ψ * min y ((N : ℝ) - y) ^ (-1 - s) := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hA0 : 0 ≤ bellConstant ℓ ψ := mul_nonneg hℓ.le (bellEnergy_nonneg hℓ)
  obtain ⟨hy0, hyN⟩ := hy
  have hmono : ∀ P : ℝ, 0 ≤ P →
      C0 * bellConstant ℓ ψ * P ≤ 3 * C0 * bellConstant ℓ ψ * P := by
    intro P hP
    have h := mul_nonneg (mul_nonneg hC0.le hA0) hP
    nlinarith
  have hexp : (-1 - s) = -s - 1 := by ring
  rcases le_total y ((N : ℝ) / 2) with hle | hle
  · have hmin : min y ((N : ℝ) - y) = y := min_eq_left (by linarith)
    rw [hmin, hexp]
    obtain ⟨h1, h2⟩ := bellKernel_half_bounds hC0 hG2 hG3 hN hℓ hψ hper hy0 hle
    have hd : deriv (bellKernel s N ℓ ψ) y = bellKernelDeriv s N ℓ ψ y :=
      (hasDerivAt_bellKernel hs0 hs1 hN hℓ hψ ⟨hy0, hyN⟩).deriv
    refine ⟨h1.trans (hmono _ (Real.rpow_nonneg hy0.le _)), ?_⟩
    rw [hd]
    exact h2
  · have hmin : min y ((N : ℝ) - y) = (N : ℝ) - y := min_eq_right (by linarith)
    rw [hmin, hexp]
    have hz : (N : ℝ) - y ∈ Ioo 0 (N : ℝ) := ⟨by linarith, by linarith⟩
    obtain ⟨h1, h2⟩ := bellKernel_half_bounds hC0 hG2 hG3 hN hℓ hψ hper hz.1 (by linarith)
    have hcomp : HasDerivAt (bellKernel s N ℓ ψ ∘ fun z : ℝ => (N : ℝ) - z)
        (bellKernelDeriv s N ℓ ψ ((N : ℝ) - y) * (-1)) y :=
      HasDerivAt.comp y (hasDerivAt_bellKernel hs0 hs1 hN hℓ hψ hz)
        ((hasDerivAt_id' y).const_sub (N : ℝ))
    have hev : bellKernel s N ℓ ψ =ᶠ[𝓝 y] (bellKernel s N ℓ ψ ∘ fun z : ℝ => (N : ℝ) - z) :=
      Eventually.of_forall fun z => (bellKernel_reflect s N hN ℓ ψ hper z).symm
    have hd : deriv (bellKernel s N ℓ ψ) y = -bellKernelDeriv s N ℓ ψ ((N : ℝ) - y) := by
      rw [(hcomp.congr_of_eventuallyEq hev).deriv]
      ring
    refine ⟨?_, ?_⟩
    · rw [← bellKernel_reflect s N hN ℓ ψ hper y]
      exact h1.trans (hmono _ (Real.rpow_nonneg hz.1.le _))
    · rw [hd, abs_neg]
      exact h2

/-- The kernel part of Lemma B.1. For `0 < s < 1` there is `C > 0`,
depending only on `s`, such that for every integer `N ≥ 1`, every `0 < ℓ ≤ 1` with `Nℓ ≥ 1`, and
every real `ψ ∈ C^∞(ℓ⁻¹𝕋)`, the averaged increment `D` and the kernel `q` satisfy the stated
bounds. The constant is `C = 3 C0`, where `C0` is the constant of
`gradient_splitting_kernel`. -/
theorem bell_kernel (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (ℓ : ℝ) (ψ : ℝ → ℝ), 1 ≤ N → 0 < ℓ → ℓ ≤ 1 →
      1 ≤ (N : ℝ) * ℓ → ContDiff ℝ ∞ ψ → Function.Periodic ψ ℓ⁻¹ →
      (∀ r : ℝ, |r| ≤ 1 / 2 →
        bellIncrement ℓ ψ r ≤ r ^ 2 * ℓ⁻¹ * bellEnergy ℓ ψ ∧
          |deriv (bellIncrement ℓ ψ) r| ≤ 2 * |r| * ℓ⁻¹ * bellEnergy ℓ ψ) ∧
      (∀ y : ℝ, y ∈ Ioo 0 (N : ℝ) → bellKernel s N ℓ ψ ((N : ℝ) - y) = bellKernel s N ℓ ψ y) ∧
      (∀ y : ℝ, y ∈ Ioo 0 (N : ℝ) →
        |bellKernel s N ℓ ψ y| ≤ C * bellConstant ℓ ψ * min y ((N : ℝ) - y) ^ (-s)) ∧
      (∀ y : ℝ, y ∈ Ioo 0 (N : ℝ) →
        |deriv (bellKernel s N ℓ ψ) y| ≤ C * bellConstant ℓ ψ * min y ((N : ℝ) - y) ^ (-1 - s)) := by
  obtain ⟨_, _, ⟨C0, hC0, hbd⟩, _, _, _, _⟩ := gradient_splitting_kernel s hs0 hs1
  have hG2 : ∀ t : ℝ, 0 < t → t ≤ 3 / 4 →
      |iteratedDeriv 2 (hurwitzKernel s) t| ≤ C0 * t ^ (-s - 2) := by
    intro t ht0 ht1
    have h := (hbd t (abs_pos.mpr ht0.ne') (by rw [abs_of_pos ht0]; exact ht1)).1 2
      (by norm_num) (by norm_num)
    simpa only [Nat.cast_ofNat, abs_of_pos ht0] using h
  have hG3 : ∀ t : ℝ, 0 < t → t ≤ 3 / 4 →
      |iteratedDeriv 3 (hurwitzKernel s) t| ≤ C0 * t ^ (-s - 3) := by
    intro t ht0 ht1
    have h := (hbd t (abs_pos.mpr ht0.ne') (by rw [abs_of_pos ht0]; exact ht1)).1 3
      (by norm_num) (by norm_num)
    simpa only [Nat.cast_ofNat, abs_of_pos ht0] using h
  refine ⟨3 * C0, by linarith, fun N ℓ ψ hN hℓ0 _ _ hψ hper => ⟨?_, ?_, ?_, ?_⟩⟩
  · intro r _
    exact ⟨bellIncrement_le hℓ0 hψ hper r, abs_deriv_bellIncrement_le hℓ0 hψ hper r⟩
  · intro y _
    exact bellKernel_reflect s N hN ℓ ψ hper y
  · intro y hy
    exact (bellKernel_bounds hC0 hG2 hG3 hN hℓ0 hψ hper hs0 hs1 hy).1
  · intro y hy
    exact (bellKernel_bounds hC0 hG2 hG3 hN hℓ0 hψ hper hs0 hs1 hy).2

end Riesz1

end
