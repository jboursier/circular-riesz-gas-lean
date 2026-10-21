/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegTransportBoundsBasic
public import Riesz1.Kernel.AdmissibilityRegularityKernel

/-!
# Uniform compact-profile tails for the unsmoothed transport

The supremum, second derivative envelope, and both tails of Lemma 5.1
hold for the same absolutely continuous representative.
The constant is chosen before the scale. The absolute value of a real lift in the
tail bounds is restricted to the central cell.
-/

public section

open MeasureTheory Set

namespace Riesz1
namespace Internal

/-- Continuous representatives with identical circle coefficients coincide everywhere.
This helper identifies representatives and imposes no additional analytic assumption. -/
theorem continuous_eq_of_transport_coeffs (L : Length)
    (f : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)})
    (P : Parameters) (ψ g : Circle L → ℝ) (hc : Continuous ψ) (hgc : Continuous g)
    (hψ : MemLp (fun x => (ψ x : ℂ)) 2 (arclength L))
    (hg : MemLp (fun x => (g x : ℂ)) 2 (arclength L))
    (hcoeff : ∀ k : ℤ, coeff L ⟨(fun x => (ψ x : ℂ)), complexL2Integrable L _ hψ⟩ k =
      transportCoeffs P L f k)
    (hcoeffg : ∀ k : ℤ, coeff L ⟨(fun x => (g x : ℂ)), complexL2Integrable L _ hg⟩ k =
      transportCoeffs P L f k) : ψ = g := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  have heqC := CircleFourier.ae_eq_of_coeff_eq hψ hg
    (fun k => (hcoeff k).trans (hcoeffg k).symm)
  have heq : ψ =ᵐ[arclength L] g := by
    filter_upwards [heqC] with x hx
    exact Complex.ofReal_injective hx
  exact Measure.eq_of_ae_eq (show ψ =ᵐ[volume] g from heq) hc hgc

end Internal

/-- Uniform compact-profile supremum, second derivative envelope and both tails in
Lemma 5.1. This partial result retains absolute continuity and the coefficients.
The global first-derivative envelope and its uniform integral bound are separate
assertions. -/
theorem exists_uniform_compact_transport_sup_secondDeriv_tails (P : Parameters)
    (p : Profile) (hp : CompactProfile p) (η B : ℝ)
    (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (α α' C₀ : ℝ)
    (hη : 0 < η) (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀)
    (hα0 : P.val.2 - 1 ≤ α) (hα1 : α < P.val.2 / 2) (hα' : α ≤ α') :
    ∃ C : ℝ, 0 < C ∧ ∀ a : Scale,
      PrimitiveRegularity (observationLength a) η P.val.2 B
        ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ →
      TransportRegularity P (observationLength a)
        ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ n marks α C₀ →
      ∃ ψ : Circle (observationLength a) → ℝ, Continuous ψ ∧
        ∃ hψ : MemLp (fun x => (ψ x : ℂ)) 2 (arclength (observationLength a)),
          (∀ k : ℤ, coeff (observationLength a)
            ⟨(fun x => (ψ x : ℂ)), complexL2Integrable _ _ hψ⟩ k =
            transportCoeffs P (observationLength a)
              ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ k) ∧
          (∀ x, |ψ x| ≤ C) ∧
          LocallyIntegrable (deriv (fun t : ℝ => ψ (t : Circle (observationLength a)))) volume ∧
          (∀ u v : ℝ, AbsolutelyContinuousOnInterval
            (fun t : ℝ => ψ (t : Circle (observationLength a))) u v) ∧
          (∀ x : ℝ, (∀ j, (x : Circle (observationLength a)) ≠
              (marks j : Circle (observationLength a))) →
            ContDiffAt ℝ 2 (fun t : ℝ => ψ (t : Circle (observationLength a))) x ∧
            |deriv (deriv (fun t : ℝ => ψ (t : Circle (observationLength a)))) x| ≤ C *
              cappedMarkDistance (fun j => (marks j : Circle (observationLength a)))
                (x : Circle (observationLength a)) ^ (-2 + P.val.2 - α')) ∧
          ∀ x : ℝ, 1 ≤ |x| → |x| ≤ (observationLength a).val / 2 →
            |deriv (fun t : ℝ => ψ (t : Circle (observationLength a))) x| ≤
              C * |x| ^ (P.val.2 - 2) ∧
            |deriv (deriv (fun t : ℝ => ψ (t : Circle (observationLength a)))) x| ≤
              C * |x| ^ (P.val.2 - 3) := by
  obtain ⟨D, hD, hbase⟩ := exists_uniform_transport_sup_secondDeriv P η B n marks
    α α' C₀ hη hB hC₀ hα0 hα1 hα'
  obtain ⟨M, _, hk⟩ := exists_uniform_transport_kernel_bounds P η B hη hB
  obtain ⟨C₁, hC₁, ht₁⟩ := hk 1 le_rfl
  obtain ⟨C₂, hC₂, ht₂⟩ := hk 2 (by norm_num)
  let I := ∫ y : ℝ, |zeroExtension p y|
  have hI : 0 ≤ I := integral_nonneg fun _ => abs_nonneg _
  let C := D + (C₁ + C₂) * I + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hDC : D ≤ C := by
    dsimp [C]
    linarith [mul_nonneg (add_pos hC₁ hC₂).le hI]
  have h₁C : C₁ * I ≤ C := by dsimp [C]; nlinarith
  have h₂C : C₂ * I ≤ C := by dsimp [C]; nlinarith
  obtain ⟨ρ, hρ0, hρ1, hsupp⟩ := hp
  refine ⟨C, hC, fun a hprim hreg => ?_⟩
  let L := observationLength a
  obtain ⟨ψ, hc, hψ, hcoeff, hsup, hi, hAC, hpoint⟩ := hbase L _ hprim hreg
  obtain ⟨g₁, hgc₁, hg₁, _, hgcoeff₁, hgpoint₁⟩ := ht₁ p a hprim
  obtain ⟨g₂, hgc₂, hg₂, _, hgcoeff₂, hgpoint₂⟩ := ht₂ p a hprim
  have heq₁ : ψ = g₁ := Internal.continuous_eq_of_transport_coeffs L _ P ψ g₁
    hc hgc₁ hψ hg₁ hcoeff hgcoeff₁
  have heq₂ : ψ = g₂ := Internal.continuous_eq_of_transport_coeffs L _ P ψ g₂
    hc hgc₂ hψ hg₂ hcoeff hgcoeff₂
  refine ⟨ψ, hc, hψ, hcoeff, fun x => (hsup x).trans hDC, hi, hAC, ?_, ?_⟩
  · intro x hx
    refine ⟨(hpoint x hx).1, (hpoint x hx).2.trans ?_⟩
    exact mul_le_mul_of_nonneg_right hDC
      (Real.rpow_nonneg (cappedMarkDistance_pos _ _ hx).le _)
  · intro x hx1 hxL
    have ht₁ := (hgpoint₁ ρ hρ0 hρ1 hsupp).2 x hx1 hxL
    have ht₂ := (hgpoint₂ ρ hρ0 hρ1 hsupp).2 x hx1 hxL
    rw [← heq₁] at ht₁
    rw [← heq₂] at ht₂
    have ht₁' : |deriv (fun t : ℝ => ψ (t : Circle L)) x| ≤
        (C₁ * I) * |x| ^ (P.val.2 - 2) := by
      simpa only [iteratedDeriv_one, Real.norm_eq_abs, Nat.cast_one,
        show P.val.2 - 1 - 1 = P.val.2 - 2 by ring] using ht₁
    have ht₂' : |deriv (deriv (fun t : ℝ => ψ (t : Circle L))) x| ≤
        (C₂ * I) * |x| ^ (P.val.2 - 3) := by
      simpa only [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_zero,
        Real.norm_eq_abs, Nat.cast_add, Nat.cast_one,
        show P.val.2 - 1 - (1 + 1) = P.val.2 - 3 by ring] using ht₂
    exact ⟨ht₁'.trans (mul_le_mul_of_nonneg_right h₁C (by positivity)),
      ht₂'.trans (mul_le_mul_of_nonneg_right h₂C (by positivity))⟩

end Riesz1
