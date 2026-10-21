/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Kernel.AdmissibilityRegularityUniformBound
public import Riesz1.Kernel.TransportScaledMain

/-!
# The continuous admissible transport agrees with the scaled kernel off the support

Fourier uniqueness identifies the bounded continuous transport with the kernel
convolution. Local equality transfers all derivatives off the periodized
support, including the derivative bounds uniform over enlarged circles.
-/

public section

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace Riesz1
namespace Internal

/-- Off the compact support the continuous representative agrees on a neighborhood with
its kernel convolution. The representative premises identify an internal analytic object. -/
theorem transport_eventuallyEq_convolution (P : Parameters) (p : Profile) (a : Scale)
    (ψ : Circle (observationLength a) → ℝ) (hc : Continuous ψ)
    (hψ : MemLp (fun x => (ψ x : ℂ)) 2 (arclength (observationLength a)))
    (hcoeff : ∀ k : ℤ, coeff (observationLength a)
      ⟨(fun x => (ψ x : ℂ)), complexL2Integrable _ _ hψ⟩ k =
      transportCoeffs P (observationLength a)
        ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ k)
    {ρ x : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2)
    (hsupp : ∀ᵐ y : ℝ, ρ ≤ |y| → zeroExtension p y = 0)
    (hx : ∀ k : ℤ, ∀ y ∈ Icc (-ρ) ρ, x ≠ y + k * (observationLength a).val) :
    (fun t : ℝ => ψ (t : Circle (observationLength a))) =ᶠ[𝓝 x]
      transportConv P.val.1 P.val.2 (observationLength a).val (zeroExtension p) := by
  let L := observationLength a
  have : Fact (0 < L.val) := ⟨L.property⟩
  obtain ⟨hconv, hconvCoeff⟩ := (transport_kernel_scaled P p a).2.2.1
  let g : Circle L → ℝ := fun z =>
    transportConv P.val.1 P.val.2 L.val (zeroExtension p) (centralRep L z)
  have heqC : (fun z => (ψ z : ℂ)) =ᵐ[arclength L] (fun z => (g z : ℂ)) := by
    apply CircleFourier.ae_eq_of_coeff_eq hψ hconv
    intro k
    exact (hcoeff k).trans (hconvCoeff k).symm
  have heq : ψ =ᵐ[arclength L] g := by
    filter_upwards [heqC] with z hz
    exact Complex.ofReal_injective hz
  have hlift : (fun t : ℝ => g (t : Circle L)) =
      transportConv P.val.1 P.val.2 L.val (zeroExtension p) := by
    funext t
    exact transportConv_centralRep _ _ _ _ _
  obtain ⟨η, hη, hsep⟩ := exists_separation L.property hx
  have hgc : ContinuousOn (fun t : ℝ => g (t : Circle L)) (Metric.ball x η) := by
    rw [hlift]
    intro t ht
    apply ((transport_kernel_scaled P p a).2.2.2.1 ρ hρ0 hρ1 hsupp t ?_).continuousAt.continuousWithinAt
    intro k y hy he
    have hh := hsep t ht y hy k
    have hz : t - y - k * L.val = 0 := by linarith
    rw [hz, abs_zero] at hh
    linarith
  have hh := eventuallyEq_lift_of_ae_eq hc heq Metric.isOpen_ball hgc
    (Metric.mem_ball_self hη)
  rw [hlift] at hh
  exact hh

/-- All classical derivatives off the support are those of the kernel convolution. -/
theorem iteratedDeriv_transport_eq_convolution (P : Parameters) (p : Profile) (a : Scale)
    (ψ : Circle (observationLength a) → ℝ) (hc : Continuous ψ)
    (hψ : MemLp (fun x => (ψ x : ℂ)) 2 (arclength (observationLength a)))
    (hcoeff : ∀ k : ℤ, coeff (observationLength a)
      ⟨(fun x => (ψ x : ℂ)), complexL2Integrable _ _ hψ⟩ k =
      transportCoeffs P (observationLength a)
        ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ k)
    {ρ x : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1 / 2)
    (hsupp : ∀ᵐ y : ℝ, ρ ≤ |y| → zeroExtension p y = 0)
    (hx : ∀ k : ℤ, ∀ y ∈ Icc (-ρ) ρ, x ≠ y + k * (observationLength a).val)
    (m : ℕ) :
    iteratedDeriv m (fun t : ℝ => ψ (t : Circle (observationLength a))) x =
      iteratedDeriv m
        (transportConv P.val.1 P.val.2 (observationLength a).val (zeroExtension p)) x := by
  exact (transport_eventuallyEq_convolution P p a ψ hc hψ hcoeff hρ0 hρ1 hsupp hx).iteratedDeriv_eq m

end Internal

/-- The continuous transport of a compact profile is smooth off its periodized support.
This is the mark-removal step. -/
theorem exists_smooth_off_support_transport (P : Parameters) (p : Profile) (a : Scale)
    (η B : ℝ) (hη : 0 < η) (hB : 0 ≤ B)
    (hprim : PrimitiveRegularity (observationLength a) η P.val.2 B
      ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩) :
    ∃ ψ : Circle (observationLength a) → ℝ, Continuous ψ ∧
      ∃ hψ : MemLp (fun x => (ψ x : ℂ)) 2 (arclength (observationLength a)),
        (∀ k : ℤ, coeff (observationLength a)
          ⟨(fun x => (ψ x : ℂ)), complexL2Integrable _ _ hψ⟩ k =
          transportCoeffs P (observationLength a)
            ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ k) ∧
        ∀ ρ : ℝ, 0 < ρ → ρ < 1 / 2 →
          (∀ᵐ y : ℝ, ρ ≤ |y| → zeroExtension p y = 0) →
          ∀ x : ℝ, (∀ k : ℤ, ∀ y ∈ Icc (-ρ) ρ,
            x ≠ y + k * (observationLength a).val) →
            ContDiffAt ℝ ∞ (fun t : ℝ => ψ (t : Circle (observationLength a))) x := by
  obtain ⟨ψ, hc, hψ, hcoeff⟩ := exists_continuous_transport_of_primitiveRegularity P
    (observationLength a) η B hη hB _ hprim
  refine ⟨ψ, hc, hψ, hcoeff, fun ρ hρ0 hρ1 hsupp x hx => ?_⟩
  exact ((transport_kernel_scaled P p a).2.2.2.1 ρ hρ0 hρ1 hsupp x hx).congr_of_eventuallyEq
    (Internal.transport_eventuallyEq_convolution P p a ψ hc hψ hcoeff hρ0 hρ1 hsupp hx)

/-- Uniform bounds for the actual continuous transport, with constants chosen before
all enlarged circles and profiles. This gives the supremum, off-support smoothness and
kernel-tail bounds. It does not assert uniform Fourier decay. -/
theorem exists_uniform_transport_kernel_bounds (P : Parameters) (η B : ℝ)
    (hη : 0 < η) (hB : 0 ≤ B) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ m : ℕ, 1 ≤ m → ∃ C : ℝ, 0 < C ∧
      ∀ (p : Profile) (a : Scale),
      PrimitiveRegularity (observationLength a) η P.val.2 B
        ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ →
      ∃ ψ : Circle (observationLength a) → ℝ, Continuous ψ ∧
        ∃ hψ : MemLp (fun x => (ψ x : ℂ)) 2 (arclength (observationLength a)),
          (∀ x, |ψ x| ≤ M) ∧
          (∀ k : ℤ, coeff (observationLength a)
            ⟨(fun x => (ψ x : ℂ)), complexL2Integrable _ _ hψ⟩ k =
            transportCoeffs P (observationLength a)
              ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ k) ∧
          ∀ ρ : ℝ, 0 < ρ → ρ < 1 / 2 →
            (∀ᵐ y : ℝ, ρ ≤ |y| → zeroExtension p y = 0) →
            (∀ x : ℝ, (∀ k : ℤ, ∀ y ∈ Icc (-ρ) ρ,
                x ≠ y + k * (observationLength a).val) →
              ContDiffAt ℝ ∞ (fun t : ℝ => ψ (t : Circle (observationLength a))) x) ∧
            ∀ x : ℝ, 1 ≤ |x| → |x| ≤ (observationLength a).val / 2 →
              ‖iteratedDeriv m (fun t : ℝ => ψ (t : Circle (observationLength a))) x‖ ≤
                C * (∫ y : ℝ, |zeroExtension p y|) * |x| ^ (P.val.2 - 1 - (m : ℝ)) := by
  obtain ⟨M, hM, hbounded⟩ := exists_uniform_bounded_transport P η B hη hB
  refine ⟨M, hM, fun m hm => ?_⟩
  obtain ⟨C, hC, htail⟩ := norm_iteratedDeriv_transportConv_le
    P.property.2.1 P.property.2.2 P.property.1 hm
  refine ⟨C, hC, fun p a hprim => ?_⟩
  let L := observationLength a
  obtain ⟨ψ, hc, hψ, hb, hcoeff⟩ := hbounded L _ hprim
  refine ⟨ψ, hc, hψ, hb, hcoeff, fun ρ hρ0 hρ1 hsupp => ⟨?_, ?_⟩⟩
  · intro x hx
    exact ((transport_kernel_scaled P p a).2.2.2.1 ρ hρ0 hρ1 hsupp x hx).congr_of_eventuallyEq
      (Internal.transport_eventuallyEq_convolution P p a ψ hc hψ hcoeff hρ0 hρ1 hsupp hx)
  · intro x hx1 hxL
    have hx : ∀ k : ℤ, ∀ y ∈ Icc (-ρ) ρ, x ≠ y + k * L.val := by
      intro k y hy he
      have hyb : |y| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
      have hsep := le_abs_sub_mul_of_mem_window hx1 hxL hyb k
      have hz : x - y - k * L.val = 0 := by linarith
      rw [hz, abs_zero] at hsep
      linarith [le_abs_self x, neg_le_abs x]
    rw [Internal.iteratedDeriv_transport_eq_convolution P p a ψ hc hψ hcoeff
      hρ0 hρ1 hsupp hx m]
    have hL1 : 1 ≤ L.val := (one_le_inv₀ a.property.1).mpr a.property.2
    have hζ := (zeroExtension_integrableOn p L).1.mono_set
      (show Ioc (-ρ) ρ ⊆ Ioc (-(L.val / 2)) (L.val / 2) from
        fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩)
    have he : ∫ y in Ioc (-ρ) ρ, |zeroExtension p y| = ∫ y : ℝ, |zeroExtension p y| :=
      MeasureTheory.setIntegral_eq_integral_of_ae_compl_eq_zero (by
        filter_upwards [hsupp] with y hy hyn
        rw [hy (le_abs_of_not_mem_Ioc hyn), abs_zero])
    have hh := htail L.val (zeroExtension p) ρ x hρ0 hρ1 hx1 hxL hζ hsupp
    rwa [he] at hh

end Riesz1
