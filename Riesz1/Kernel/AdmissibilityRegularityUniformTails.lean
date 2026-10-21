/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.AdmissibilityRegularityKernel

/-!
# Uniform tails for every continuous representative of the compact transport

The same continuous representative used for (A2)–(A3) has the two kernel derivative
bounds. Constants precede the observation scale.
-/

public section

open MeasureTheory Set
open scoped ContDiff

namespace Riesz1.Internal

/-- The first two derivative tails of any continuous transport representative. The
representative hypotheses identify an internal object, rather than assuming decay. -/
theorem uniform_transport_derivative_tails (P : Parameters) (p : Profile)
    (hp : CompactProfile p) :
    ∃ M C : ℝ, 0 ≤ M ∧ 0 ≤ C ∧ ∀ (a : Scale)
      (ψ : Circle (observationLength a) → ℝ), Continuous ψ →
      ∀ hψ : MemLp (fun x => (ψ x : ℂ)) 2 (arclength (observationLength a)),
      (∀ k : ℤ, coeff (observationLength a)
        ⟨(fun x => (ψ x : ℂ)), complexL2Integrable _ _ hψ⟩ k =
          transportCoeffs P (observationLength a)
            ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ k) →
      ∀ x : ℝ, 1 ≤ |x| → |x| ≤ (observationLength a).val / 2 →
        DifferentiableAt ℝ (deriv (fun t : ℝ => ψ (t : Circle (observationLength a)))) x ∧
        |deriv (fun t : ℝ => ψ (t : Circle (observationLength a))) x| ≤ M ∧
        |deriv (deriv (fun t : ℝ => ψ (t : Circle (observationLength a)))) x| ≤
          C * |x| ^ (P.val.2 - 3) := by
  obtain ⟨ρ, hρ0, hρ1, hsupp⟩ := hp
  obtain ⟨C1, hC1, ht1⟩ := norm_iteratedDeriv_transportConv_le
    P.property.2.1 P.property.2.2 P.property.1 (m := 1) le_rfl
  obtain ⟨C2, hC2, ht2⟩ := norm_iteratedDeriv_transportConv_le
    P.property.2.1 P.property.2.2 P.property.1 (m := 2) (by norm_num)
  let Z := ∫ y : ℝ, |zeroExtension p y|
  have hZ : 0 ≤ Z := integral_nonneg fun _ => abs_nonneg _
  refine ⟨C1 * Z, C2 * Z, mul_nonneg hC1.le hZ, mul_nonneg hC2.le hZ,
    fun a ψ hc hψ hcoeff x hx hxL => ?_⟩
  let L := observationLength a
  have hL1 : 1 ≤ L.val := (one_le_inv₀ a.property.1).mpr a.property.2
  have hxoff : ∀ k : ℤ, ∀ y ∈ Icc (-ρ) ρ, x ≠ y + k * L.val := by
    intro k y hy he
    have hyb : |y| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hh := le_abs_sub_mul_of_mem_window hx hxL hyb k
    have hz : x - y - k * L.val = 0 := by linarith
    rw [hz, abs_zero] at hh
    linarith
  have heq := transport_eventuallyEq_convolution P p a ψ hc hψ hcoeff
    hρ0 hρ1 hsupp hxoff
  have hsmooth := ((transport_kernel_scaled P p a).2.2.2.1 ρ hρ0 hρ1 hsupp x hxoff).congr_of_eventuallyEq heq
  have hζ := (zeroExtension_integrableOn p L).1.mono_set
    (show Ioc (-ρ) ρ ⊆ Ioc (-(L.val / 2)) (L.val / 2) from
      fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩)
  have hint : (∫ y in Ioc (-ρ) ρ, |zeroExtension p y|) = Z := by
    apply MeasureTheory.setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [hsupp] with y hy hyn
    rw [hy (le_abs_of_not_mem_Ioc hyn), abs_zero]
  have hd1 := ht1 L.val (zeroExtension p) ρ x hρ0 hρ1 hx hxL hζ hsupp
  have hd2 := ht2 L.val (zeroExtension p) ρ x hρ0 hρ1 hx hxL hζ hsupp
  rw [← heq.iteratedDeriv_eq 1, hint] at hd1
  rw [← heq.iteratedDeriv_eq 2, hint] at hd2
  simp only [iteratedDeriv_succ, iteratedDeriv_zero,
    Nat.cast_one, Nat.cast_ofNat, Real.norm_eq_abs] at hd1 hd2
  refine ⟨(hsmooth.derivWithin (m := 1) (by simp)).differentiableAt (by simp), ?_, ?_⟩
  · exact hd1.trans (by
      have hh := Real.rpow_le_one_of_one_le_of_nonpos hx
        (by linarith [P.property.2.2] : P.val.2 - 1 - 1 ≤ 0)
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hh (mul_nonneg hC1.le hZ))
  · simpa only [show P.val.2 - 1 - 2 = P.val.2 - 3 by ring] using hd2

end Riesz1.Internal
