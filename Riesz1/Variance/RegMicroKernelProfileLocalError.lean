/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroKernelProfileDerivative
public import Riesz1.ToMathlib.FiniteMarkMollifyError
public import Riesz1.Variance.RegTransportBoundsFixedCircle
public import Riesz1.Variance.RegTransportBoundsCompact

/-!
# Local profile regularization errors

The first derivative estimate gives `|e_h| ≤ C h r^(-1-α)` for `h ≤ r`,
with constants uniform in the compact case. This supplies the value estimates
on fixed regions away from the marks and on `2h ≤ r ≤ 4h` in Lemma 5.3
without presupposing global values at the marks.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Riesz1
namespace Internal

/-- Local error bound from the quantitative inverse estimate on the same
transport. The hypotheses are internal. The two statements below
supply them from profile regularity. -/
theorem uniform_inverse_profile_local_error (P : Parameters) (ρ : ℝ → ℝ)
    (hρ : IsMollifier ρ) (α : ℝ)
    (hα0 : P.val.2 - 1 < α) (hα1 : α < P.val.2 / 2) (n : ℕ+) :
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
        (∀ᵐ x : ℝ ∂(volume.restrict (Ioc (-(L.val / 2)) (L.val / 2))),
          f.val (x : Circle L) = m + inverseConv P L.val q x) ∧
        ∀ h : ℝ, 0 < h → ∀ x : ℝ,
          (∀ j, (x : Circle L) ≠ (marks j : Circle L)) →
          h ≤ cappedMarkDistance (fun j => (marks j : Circle L)) (x : Circle L) →
          |m + inverseConv P L.val q x -
            circleMollify ρ L.val h (fun y => f.val (y : Circle L)) x| ≤
              K * A * h * cappedMarkDistance (fun j => (marks j : Circle L))
                (x : Circle L) ^ (-1 - α) := by
  obtain ⟨K₀, hK₀, hprofile⟩ := uniform_inverse_profile_derivative P α hα0 hα1 n
  refine ⟨K₀ * (1 / 2 : ℝ) ^ (-1 - α), by positivity,
    fun L f marks ψ hc hcoeff hi A hA hpoint => ?_⟩
  have : Fact (0 < L.val) := ⟨L.property⟩
  let q := deriv (fun t : ℝ => ψ.val (t : Circle L))
  let m := (∫ y in Ioc (-(L.val / 2)) (L.val / 2), f.val (y : Circle L)) / L.val
  let F := fun t => m + inverseConv P L.val q t
  obtain ⟨hrep, hprof⟩ := hprofile L f marks ψ hc hcoeff hi A hA hpoint
  have hqi : IntegrableOn q (Ioc (-(L.val / 2)) (L.val / 2)) :=
    (hi.integrableOn_isCompact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hconvI := PeriodicConvolution.locallyIntegrable_of_period L.property
    (inverseConv_periodic P L.property q) (integrableOn_inverseConv P L.property hqi)
  have hFi : LocallyIntegrable F volume := (locallyIntegrable_const m).add hconvI
  have hFp : Function.Periodic F L.val := fun t => by
    dsimp only [F]
    rw [inverseConv_periodic P L.property q t]
  refine ⟨hrep, fun h hh x hx hhr => ?_⟩
  have hmoll : circleMollify ρ L.val h (fun y => f.val (y : Circle L)) x =
      circleMollify ρ L.val h F x := by
    unfold circleMollify
    rw [intervalIntegral.integral_of_le (by linarith [L.property]),
      intervalIntegral.integral_of_le (by linarith [L.property])]
    apply integral_congr_ae
    filter_upwards [hrep] with y hy
    rw [hy]
  rw [hmoll]
  have hv := circleMollify_sub_le_of_marked_deriv marks hρ hFi hFp
    (mul_nonneg hK₀.le hA) (by linarith [P.property.2.1] : -1 ≤ α)
    (fun y hy => (hprof y hy).2) hh hx hhr
  exact hv.trans_eq (by ring)

end Internal

/-- The local value bound for a macroscopic profile. On
`r ≥ δ > 0` it gives `O(h)`. On `2h ≤ r ≤ 4h` it gives `O(h^(-α))`. -/
theorem regMicroKernel_profile_local_error_macroscopic (P : Parameters) (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) (p : Profile)
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
         ∀ h : ℝ, 0 < h → ∀ x : ℝ,
           (∀ j, (x : Circle L) ≠ (marks j : Circle L)) →
           h ≤ cappedMarkDistance (fun j => (marks j : Circle L)) (x : Circle L) →
           |m + inverseConv P L.val q x - circleMollify ρ L.val h (fun y => p.val (y : Circle L)) x| ≤
             C * h * cappedMarkDistance (fun j => (marks j : Circle L))
               (x : Circle L) ^ (-1 - α)) := by
  obtain ⟨K, hK, hprofile⟩ := Internal.uniform_inverse_profile_local_error P ρ hρ α hα0 hα1 n
  obtain ⟨A, hA, ψ, hc, hψ, hcoeff, hi, _hAC, _hsup, hpoint⟩ :=
    macroscopic_regTransportBounds P p η B n marks α α C₀ hη hB hC₀ hα0.le hα1 le_rfl hα0
      hprim hreg
  refine ⟨K * A, mul_pos hK hA, ⟨ψ, hψ⟩, hc, hcoeff, ?_⟩
  exact hprofile unitLength ⟨p.val, p.property⟩ marks ⟨ψ, hψ⟩ hc hcoeff hi A hA.le hpoint

/-- The local value bound of Lemma 5.3 for compact profiles.
The constant precedes the shrinking sequence, its particle index, and every
additional observation scale satisfying the same regularity data. -/
theorem regMicroKernel_profile_local_error_compact (P : Parameters)
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
         ∀ h : ℝ, 0 < h → ∀ x : ℝ,
           (∀ j, (x : Circle L) ≠ (marks j : Circle L)) →
           h ≤ cappedMarkDistance (fun j => (marks j : Circle L)) (x : Circle L) →
           |m + inverseConv P L.val q x - circleMollify ρ L.val h (fun y => periodizedProfile p L (y : Circle L)) x| ≤
             C * h * cappedMarkDistance (fun j => (marks j : Circle L))
               (x : Circle L) ^ (-1 - α)) := by
  obtain ⟨K, hK, hprofile⟩ := Internal.uniform_inverse_profile_local_error P ρ hρ α hα0 hα1 n
  obtain ⟨A, hA, htransport⟩ := compact_regTransportBounds P p hp η B n marks α α C₀
    hη hB hC₀ hα0.le hα1 le_rfl hα0 hα1
  refine ⟨K * A, mul_pos hK hA, fun ell hell hfamily a hprim hreg => ?_⟩
  obtain ⟨ψ, hc, hψ, hcoeff, hi, _hAC, _hsup, hpoint, _htail⟩ :=
    htransport ell hell hfamily a hprim hreg
  exact ⟨⟨ψ, hψ⟩, hc, hcoeff, hprofile (observationLength a)
    ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ marks
      ⟨ψ, hψ⟩ hc hcoeff hi A hA.le hpoint⟩

end Riesz1
