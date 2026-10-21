/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroKernelDerivativeBound
public import Riesz1.Variance.RegTransportBoundsFixedCircle
public import Riesz1.Variance.RegTransportBoundsCompact

/-!
# The first profile derivative bound from admissibility

The inverse-transport representative has derivative bounded by
`C r^(-1-α)` off the marks, in both the macroscopic and compact cases.
In the compact case the constant precedes every scale sequence and every
observation circle. This proves equation (5.7) of Lemma 5.3. The other conclusions of
that lemma are separate.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace Riesz1
namespace Internal

/-- The quantitative inverse estimate and Fourier representation on the same
transport. The constant precedes all circle-specific data. The pointwise
envelopes are internal hypotheses supplied by the two results below. -/
theorem uniform_inverse_profile_derivative (P : Parameters) (α : ℝ)
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
        ∀ x : ℝ, (∀ j, (x : Circle L) ≠ (marks j : Circle L)) →
          IntegrableOn (fun y => q y * inverseKernel P L.val (x - y))
            (Ioc (-(L.val / 2)) (L.val / 2)) ∧
          DifferentiableAt ℝ (fun t => m + inverseConv P L.val q t) x ∧
          |deriv (fun t => m + inverseConv P L.val q t) x| ≤ K * A *
            cappedMarkDistance (fun j => (marks j : Circle L)) (x : Circle L) ^ (-1 - α) := by
  let b := 1 - P.val.2 + α
  have hb : 0 < b := by dsimp [b]; linarith
  have hb1 : b < 1 := by dsimp [b]; linarith [P.property.2.1]
  obtain ⟨K, hK, hderiv⟩ := inverseConv_deriv_bound P hb hb1 (Fin (n : ℕ))
  refine ⟨K, hK, fun L f marks ψ hc hcoeff hi A hA hpoint => ?_⟩
  have : Fact (0 < L.val) := ⟨L.property⟩
  let q := deriv (fun t : ℝ => ψ.val (t : Circle L))
  let m := (∫ y in Ioc (-(L.val / 2)) (L.val / 2), f.val (y : Circle L)) / L.val
  have hcount := CircleSingularity.countable_marked_lifts (T := L.val) marks
  have hdiff : ∀ x : ℝ, x ∉ {t : ℝ | ∃ j, (t : Circle L) = (marks j : Circle L)} →
      DifferentiableAt ℝ (fun t : ℝ => ψ.val (t : Circle L)) x := by
    intro x hx
    exact (hpoint x (by simpa only [mem_ofPred_eq, not_exists] using hx)).1.differentiableAt
      (by norm_num)
  have hper : Function.Periodic (fun t : ℝ => ψ.val (t : Circle L)) L.val := fun t => by
    dsimp only
    rw [AddCircle.coe_add_period]
  have hrep := inverse_representation P L f ψ hc hcount hdiff
    ((hi.integrableOn_isCompact isCompact_uIcc).intervalIntegrable) hcoeff
  have hqb (y : ℝ) (hy : ∀ j, (y : Circle L) ≠ (marks j : Circle L)) :
      ContDiffAt ℝ 1 q y ∧
        |q y| ≤ A * cappedMarkDistance (fun j => (marks j : Circle L)) (y : Circle L) ^ (-b) ∧
        |deriv q y| ≤ A * cappedMarkDistance (fun j => (marks j : Circle L)) (y : Circle L) ^ (-1 - b) := by
    obtain ⟨hs, hq, hq'⟩ := hpoint y hy
    refine ⟨hs.derivWithin (m := 1) (by norm_num), ?_, ?_⟩
    · simpa only [b, show -(1 - P.val.2 + α) = -1 + P.val.2 - α by ring] using hq
    · simpa only [b, show -1 - (1 - P.val.2 + α) = -2 + P.val.2 - α by ring] using hq'
  refine ⟨hrep, fun x hx => ?_⟩
  obtain ⟨hxi, hxd, hxb⟩ := hderiv L.val marks q A hA (measurable_deriv _)
    (deriv_periodic_of hper) hi hqb x hx
  refine ⟨hxi, hxd.const_add m, ?_⟩
  rw [deriv_const_add]
  simpa only [b, show -P.val.2 - (1 - P.val.2 + α) = -1 - α by ring] using hxb

end Internal

/-- The first derivative bound of Lemma 5.3 for a macroscopic
profile. Every input is profile data. The inverse representative and
its absolute-integrability certificates are conclusions. -/
theorem regMicroKernel_profile_derivative_macroscopic (P : Parameters) (p : Profile)
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
         ∀ x : ℝ, (∀ j, (x : Circle L) ≠ (marks j : Circle L)) →
           IntegrableOn (fun y => q y * inverseKernel P L.val (x - y))
             (Ioc (-(L.val / 2)) (L.val / 2)) ∧
           DifferentiableAt ℝ (fun t => m + inverseConv P L.val q t) x ∧
           |deriv (fun t => m + inverseConv P L.val q t) x| ≤ C *
             cappedMarkDistance (fun j => (marks j : Circle L)) (x : Circle L) ^ (-1 - α)) := by
  obtain ⟨K, hK, hprofile⟩ := Internal.uniform_inverse_profile_derivative P α hα0 hα1 n
  obtain ⟨A, hA, ψ, hc, hψ, hcoeff, hi, _hAC, _hsup, hpoint⟩ :=
    macroscopic_regTransportBounds P p η B n marks α α C₀ hη hB hC₀ hα0.le hα1 le_rfl hα0
      hprim hreg
  refine ⟨K * A, mul_pos hK hA, ⟨ψ, hψ⟩, hc, hcoeff, ?_⟩
  exact hprofile unitLength ⟨p.val, p.property⟩ marks ⟨ψ, hψ⟩ hc hcoeff hi A hA.le hpoint

/-- The first derivative bound of Lemma 5.3 for compact profiles.
The constant precedes the shrinking sequence, its particle index, and every
additional observation scale satisfying the same regularity data. -/
theorem regMicroKernel_profile_derivative_compact (P : Parameters)
    (p : Profile) (hp : CompactProfile p) (η B : ℝ)
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
         ∀ x : ℝ, (∀ j, (x : Circle L) ≠ (marks j : Circle L)) →
           IntegrableOn (fun y => q y * inverseKernel P L.val (x - y))
             (Ioc (-(L.val / 2)) (L.val / 2)) ∧
           DifferentiableAt ℝ (fun t => m + inverseConv P L.val q t) x ∧
           |deriv (fun t => m + inverseConv P L.val q t) x| ≤ C *
             cappedMarkDistance (fun j => (marks j : Circle L)) (x : Circle L) ^ (-1 - α)) := by
  obtain ⟨K, hK, hprofile⟩ := Internal.uniform_inverse_profile_derivative P α hα0 hα1 n
  obtain ⟨A, hA, htransport⟩ := compact_regTransportBounds P p hp η B n marks α α C₀
    hη hB hC₀ hα0.le hα1 le_rfl hα0 hα1
  refine ⟨K * A, mul_pos hK hA, fun ell hell hfamily a hprim hreg => ?_⟩
  obtain ⟨ψ, hc, hψ, hcoeff, hi, _hAC, _hsup, hpoint, _htail⟩ :=
    htransport ell hell hfamily a hprim hreg
  exact ⟨⟨ψ, hψ⟩, hc, hcoeff, hprofile (observationLength a)
    ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ marks
      ⟨ψ, hψ⟩ hc hcoeff hi A hA.le hpoint⟩

end Riesz1
