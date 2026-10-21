/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroKernelErrorDerivativeBound
public import Riesz1.Variance.RegMicroKernelProfileDerivative
public import Riesz1.Variance.RegMicroKernelErrorRepresentation

/-!
# Both profile derivatives from admissibility

The same continuous transport supplies the inverse representative and the
actual regularization error. The quantitative error estimate holds at every
unmarked point, hence in particular for `r ≥ 2h` as required by
equation (5.8) of Lemma 5.3.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Riesz1.Internal

/-- Uniform analytic application on one transport. All envelope assumptions
are internal and are supplied by the regularity predicates downstream. -/
theorem uniform_inverse_profile_error_derivative (P : Parameters) (ρ : ℝ → ℝ)
    (hρ : IsMollifier ρ) (α : ℝ) (hα0 : P.val.2 - 1 < α)
    (hα1 : α < P.val.2 / 2) (n : ℕ+) :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : Length)
      (f : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)})
      (marks : Fin (n : ℕ) → ℝ)
      (ψ : {g : Circle L → ℝ // MemLp (fun x => (g x : ℂ)) 2 (arclength L)}),
      Continuous ψ.val →
      (∀ k : ℤ, coeff L
        ⟨(fun x => (ψ.val x : ℂ)), complexL2Integrable L _ ψ.property⟩ k =
          transportCoeffs P L f k) →
      LocallyIntegrable (deriv (fun t : ℝ => ψ.val (t : Circle L))) volume →
      ∀ A : ℝ, 0 ≤ A →
        (∀ x : ℝ, (∀ j, (x : Circle L) ≠ (marks j : Circle L)) →
          ContDiffAt ℝ 2 (fun t : ℝ => ψ.val (t : Circle L)) x ∧
          |deriv (fun t : ℝ => ψ.val (t : Circle L)) x| ≤ A *
            cappedMarkDistance (fun j => (marks j : Circle L)) (x : Circle L) ^ (-1 + P.val.2 - α) ∧
          |deriv (deriv (fun t : ℝ => ψ.val (t : Circle L))) x| ≤ A *
            cappedMarkDistance (fun j => (marks j : Circle L)) (x : Circle L) ^ (-2 + P.val.2 - α)) →
        let m := (∫ y in Ioc (-(L.val / 2)) (L.val / 2), f.val (y : Circle L)) / L.val
        let q := deriv (fun t : ℝ => ψ.val (t : Circle L))
        let F := fun t => m + inverseConv P L.val q t
        (∀ᵐ x : ℝ ∂(volume.restrict (Ioc (-(L.val / 2)) (L.val / 2))), f.val (x : Circle L) = F x) ∧
        (∀ x : ℝ, (∀ j, (x : Circle L) ≠ (marks j : Circle L)) →
          DifferentiableAt ℝ F x ∧ |deriv F x| ≤ K * A *
            cappedMarkDistance (fun j => (marks j : Circle L)) (x : Circle L) ^ (-1 - α)) ∧
        ∀ h : ℝ, 0 < h → h ≤ L.val / 4 →
          let e := fun t => F t - circleMollify ρ L.val h (fun y => f.val (y : Circle L)) t
          ∀ x : ℝ, (∀ j, (x : Circle L) ≠ (marks j : Circle L)) →
            DifferentiableAt ℝ e x ∧ |deriv e x| ≤ K * A * h ^ (1 - P.val.2) *
              cappedMarkDistance (fun j => (marks j : Circle L)) (x : Circle L) ^ (-2 + P.val.2 - α) := by
  let b := 1 - P.val.2 + α
  have hb : 0 < b := by dsimp [b]; linarith
  have hb1 : b < 1 := by dsimp [b]; linarith [P.property.2.1]
  obtain ⟨K₀, hK₀, hprofile⟩ := uniform_inverse_profile_derivative P α hα0 hα1 n
  obtain ⟨J, hJ, herr⟩ := errorConv_deriv_bound P ρ hρ hb hb1 (Fin (n : ℕ))
  refine ⟨K₀ + J, by positivity, fun L f marks ψ hc hcoeff hi A hA hpoint => ?_⟩
  have : Fact (0 < L.val) := ⟨L.property⟩
  let q := deriv (fun t : ℝ => ψ.val (t : Circle L))
  let m := (∫ y in Ioc (-(L.val / 2)) (L.val / 2), f.val (y : Circle L)) / L.val
  let F := fun t => m + inverseConv P L.val q t
  obtain ⟨hrep, hprof⟩ := hprofile L f marks ψ hc hcoeff hi A hA hpoint
  have hqi : IntegrableOn q (Ioc (-(L.val / 2)) (L.val / 2)) :=
    (hi.integrableOn_isCompact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hconvI := PeriodicConvolution.locallyIntegrable_of_period L.property
    (inverseConv_periodic P L.property q) (integrableOn_inverseConv P L.property hqi)
  have hqp : Function.Periodic q L.val := deriv_periodic_of (fun t => by
    rw [AddCircle.coe_add_period])
  have hqb (y : ℝ) (hy : ∀ j, (y : Circle L) ≠ (marks j : Circle L)) :
      ContDiffAt ℝ 1 q y ∧
        |q y| ≤ A * cappedMarkDistance (fun j => (marks j : Circle L)) (y : Circle L) ^ (-b) ∧
        |deriv q y| ≤ A * cappedMarkDistance (fun j => (marks j : Circle L)) (y : Circle L) ^ (-1 - b) := by
    obtain ⟨hs, hq, hq'⟩ := hpoint y hy
    refine ⟨hs.derivWithin (m := 1) (by norm_num), ?_, ?_⟩
    · simpa only [b, show -(1 - P.val.2 + α) = -1 + P.val.2 - α by ring] using hq
    · simpa only [b, show -1 - (1 - P.val.2 + α) = -2 + P.val.2 - α by ring] using hq'
  refine ⟨hrep, fun x hx => ⟨(hprof x hx).2.1, (hprof x hx).2.2.trans ?_⟩, ?_⟩
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : K₀ ≤ K₀ + J) hA)
      (Real.rpow_nonneg (cappedMarkDistance_pos _ _ hx).le _)
  · intro h hh hhL
    let E := fun t => inverseKernel P L.val t - mollifyLine ρ h (inverseKernel P L.val) t
    let e := fun t => F t - circleMollify ρ L.val h (fun y => f.val (y : Circle L)) t
    let v := fun t => ∫ y in Ioc (-(L.val / 2)) (L.val / 2), q y * E (t - y)
    have hmoll (t : ℝ) : circleMollify ρ L.val h (fun y => f.val (y : Circle L)) t =
        circleMollify ρ L.val h F t := by
      unfold circleMollify
      rw [intervalIntegral.integral_of_le (by linarith [L.property]),
        intervalIntegral.integral_of_le (by linarith [L.property])]
      apply integral_congr_ae
      filter_upwards [hrep] with y hy
      rw [hy]
    have he (t : ℝ) : e t = inverseConv P L.val q t - circleMollify ρ L.val h (inverseConv P L.val q) t := by
      dsimp only [e, F]
      rw [hmoll t, circleMollify_const_add hρ L.property hh hconvI
        (inverseConv_periodic P L.property q) m t]
      ring
    have hv (x : ℝ) (hx : ∀ j, (x : Circle L) ≠ (marks j : Circle L)) : e x = v x := by
      rw [he x]
      exact (inverseConv_sub_smoothing_of_integrable P hρ L.property hh
        (by linarith) hqi (hprof x hx).1).2
    change ∀ x : ℝ, (∀ j, (x : Circle L) ≠ (marks j : Circle L)) →
      DifferentiableAt ℝ e x ∧ |deriv e x| ≤ (K₀ + J) * A * h ^ (1 - P.val.2) *
        cappedMarkDistance (fun j => (marks j : Circle L)) (x : Circle L) ^ (-2 + P.val.2 - α)
    intro x hx
    have hloc : e =ᶠ[𝓝 x] v := by
      filter_upwards [(isOpen_unmarked_lift marks).mem_nhds hx] with t ht
      exact hv t ht
    obtain ⟨_hEi, hved, hveb⟩ := herr L.val marks q A hA (measurable_deriv _)
      hqp hi hqb h hh hhL x hx
    refine ⟨hved.congr_of_eventuallyEq hloc, ?_⟩
    rw [hloc.deriv_eq]
    apply hveb.trans
    have heq : -1 - b = -2 + P.val.2 - α := by dsimp [b]; ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : J ≤ K₀ + J) hA)
        (Real.rpow_nonneg hh.le _))
      (Real.rpow_nonneg (cappedMarkDistance_pos _ _ hx).le _)

end Riesz1.Internal

namespace Riesz1

/-- Both derivative bounds of Lemma 5.3 for a macroscopic
profile. Every input is profile data. The error estimate holds at every
unmarked point, including the required region `r ≥ 2h`. -/
theorem regMicroKernel_profile_error_derivative_macroscopic (P : Parameters) (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) (p : Profile)
    (η B : ℝ) (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (α C₀ : ℝ)
    (hη : 0 < η) (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀)
    (hα0 : P.val.2 - 1 < α) (hα1 : α < P.val.2 / 2)
    (hprim : PrimitiveRegularity unitLength η P.val.2 B ⟨p.val, p.property⟩)
    (hreg : TransportRegularity P unitLength ⟨p.val, p.property⟩ n marks α C₀) :
    ∃ C : ℝ, 0 < C ∧
      ∃ ψ : {g : Circle unitLength → ℝ // MemLp (fun x => (g x : ℂ)) 2 (arclength unitLength)},
        Continuous ψ.val ∧
        (∀ k : ℤ, coeff unitLength
          ⟨(fun x => (ψ.val x : ℂ)), complexL2Integrable unitLength _ ψ.property⟩ k =
            transportCoeffs P unitLength ⟨p.val, p.property⟩ k) ∧
        (let L := unitLength
         let m := (∫ y in Ioc (-(L.val / 2)) (L.val / 2), p.val (y : Circle L)) / L.val
         let q := deriv (fun t : ℝ => ψ.val (t : Circle L))
         (∀ᵐ x : ℝ ∂(volume.restrict (Ioc (-(L.val / 2)) (L.val / 2))),
           p.val (x : Circle L) = m + inverseConv P L.val q x) ∧
         (∀ x : ℝ, (∀ j, (x : Circle L) ≠ (marks j : Circle L)) →
           DifferentiableAt ℝ (fun t => m + inverseConv P L.val q t) x ∧
           |deriv (fun t => m + inverseConv P L.val q t) x| ≤ C *
             cappedMarkDistance (fun j => (marks j : Circle L)) (x : Circle L) ^ (-1 - α)) ∧
         ∀ h : ℝ, 0 < h → h ≤ L.val / 4 →
           let e := fun t => m + inverseConv P L.val q t -
             circleMollify ρ L.val h (fun y => p.val (y : Circle L)) t
           ∀ x : ℝ, (∀ j, (x : Circle L) ≠ (marks j : Circle L)) →
             DifferentiableAt ℝ e x ∧ |deriv e x| ≤ C * h ^ (1 - P.val.2) *
               cappedMarkDistance (fun j => (marks j : Circle L)) (x : Circle L) ^ (-2 + P.val.2 - α)) := by
  obtain ⟨K, hK, hprofile⟩ := Internal.uniform_inverse_profile_error_derivative P ρ hρ α hα0 hα1 n
  obtain ⟨A, hA, ψ, hc, hψ, hcoeff, hi, _hAC, _hsup, hpoint⟩ :=
    macroscopic_regTransportBounds P p η B n marks α α C₀ hη hB hC₀ hα0.le hα1 le_rfl hα0
      hprim hreg
  refine ⟨K * A, mul_pos hK hA, ⟨ψ, hψ⟩, hc, hcoeff, ?_⟩
  exact hprofile unitLength ⟨p.val, p.property⟩ marks ⟨ψ, hψ⟩ hc hcoeff hi A hA.le hpoint

/-- Both derivative bounds of Lemma 5.3 for compact profiles.
The constant precedes the shrinking sequence, its particle index, and every
additional observation scale satisfying the same regularity data. -/
theorem regMicroKernel_profile_error_derivative_compact (P : Parameters)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) (p : Profile) (hp : CompactProfile p) (η B : ℝ)
    (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (α C₀ : ℝ)
    (hη : 0 < η) (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀)
    (hα0 : P.val.2 - 1 < α) (hα1 : α < P.val.2 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ ell : Scales,
      Tendsto (fun k : ℕ => (ell ⟨k + 1, Nat.succ_pos k⟩).val) atTop (𝓝 0) →
      (∀ N, PrimitiveRegularity (observationLength (ell N)) η P.val.2 B
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ ∧
        TransportRegularity P (observationLength (ell N))
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩
            n marks α C₀) → ∀ a : Scale,
      PrimitiveRegularity (observationLength a) η P.val.2 B
        ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ →
      TransportRegularity P (observationLength a)
        ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ n marks α C₀ →
      let L := observationLength a
      ∃ ψ : {g : Circle L → ℝ // MemLp (fun x => (g x : ℂ)) 2 (arclength L)},
        Continuous ψ.val ∧
        (∀ k : ℤ, coeff L
          ⟨(fun x => (ψ.val x : ℂ)), complexL2Integrable L _ ψ.property⟩ k =
            transportCoeffs P L ⟨periodizedProfile p L, periodizedProfileL2 p a⟩ k) ∧
        (let m := (∫ y in Ioc (-(L.val / 2)) (L.val / 2), periodizedProfile p L (y : Circle L)) / L.val
         let q := deriv (fun t : ℝ => ψ.val (t : Circle L))
         (∀ᵐ x : ℝ ∂(volume.restrict (Ioc (-(L.val / 2)) (L.val / 2))),
           periodizedProfile p L (x : Circle L) = m + inverseConv P L.val q x) ∧
         (∀ x : ℝ, (∀ j, (x : Circle L) ≠ (marks j : Circle L)) →
           DifferentiableAt ℝ (fun t => m + inverseConv P L.val q t) x ∧
           |deriv (fun t => m + inverseConv P L.val q t) x| ≤ C *
             cappedMarkDistance (fun j => (marks j : Circle L)) (x : Circle L) ^ (-1 - α)) ∧
         ∀ h : ℝ, 0 < h → h ≤ L.val / 4 →
           let e := fun t => m + inverseConv P L.val q t -
             circleMollify ρ L.val h (fun y => periodizedProfile p L (y : Circle L)) t
           ∀ x : ℝ, (∀ j, (x : Circle L) ≠ (marks j : Circle L)) →
             DifferentiableAt ℝ e x ∧ |deriv e x| ≤ C * h ^ (1 - P.val.2) *
               cappedMarkDistance (fun j => (marks j : Circle L)) (x : Circle L) ^ (-2 + P.val.2 - α)) := by
  obtain ⟨K, hK, hprofile⟩ := Internal.uniform_inverse_profile_error_derivative P ρ hρ α hα0 hα1 n
  obtain ⟨A, hA, htransport⟩ := compact_regTransportBounds P p hp η B n marks α α C₀
    hη hB hC₀ hα0.le hα1 le_rfl hα0 hα1
  refine ⟨K * A, mul_pos hK hA, fun ell hell hfamily a hprim hreg => ?_⟩
  obtain ⟨ψ, hc, hψ, hcoeff, hi, _hAC, _hsup, hpoint, _htail⟩ :=
    htransport ell hell hfamily a hprim hreg
  exact ⟨⟨ψ, hψ⟩, hc, hcoeff, hprofile (observationLength a)
    ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ marks
      ⟨ψ, hψ⟩ hc hcoeff hi A hA.le hpoint⟩

end Riesz1
