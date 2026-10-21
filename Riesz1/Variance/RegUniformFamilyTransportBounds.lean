/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegUniformFamilyTransport

/-! # Uniform transport bounds for the smoothing families

Lemma 5.1, uniform in the family radius and the subsequent
smoothing radius, with exact coefficient identities for both transports.
-/

public section

open MeasureTheory Filter
open scoped ContDiff Topology

namespace Riesz1

/-- Uniform near-mark bounds and supremum for both compact transport families.
The first Fourier identity is the multiplier of the regularized transport.
The second is the transport of the error. -/
theorem regUniform_familyTransport_compact (P : Parameters) (p : Profile) (hp : CompactProfile p)
    (η B : ℝ) (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (α α' C₀ : ℝ)
    (hη : 0 < η) (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀)
    (hα0 : P.val.2 - 1 ≤ α) (hα1 : α < P.val.2 / 2) (hα' : α ≤ α')
    (hα'0 : P.val.2 - 1 < α') (hα'1 : α' < P.val.2 / 2)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ell : Scales,
      Tendsto (fun k : ℕ => (ell ⟨k + 1, Nat.succ_pos k⟩).val) atTop (𝓝 0) →
      (∀ N, PrimitiveRegularity (observationLength (ell N)) η P.val.2 B
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ ∧
        TransportRegularity P (observationLength (ell N))
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩
            n marks α C₀) →
      ∀ a : Scale,
        PrimitiveRegularity (observationLength a) η P.val.2 B
          ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ →
        TransportRegularity P (observationLength a)
          ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ n marks α C₀ →
        let L := observationLength a
        ∃ ψ : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)},
          Continuous ψ.val ∧ (∀ k, coeff L ⟨(fun x => (ψ.val x : ℂ)), complexL2Integrable L _ ψ.property⟩ k =
            transportCoeffs P L ⟨periodizedProfile p L, periodizedProfileL2 p a⟩ k) ∧
          ∀ t : ℝ, 0 < t → t ≤ 1 →
          ∃ φ χ : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)},
            (∀ x : ℝ, φ.val (x : Circle L) = circleMollify ρ L.val t
              (fun y : ℝ => ψ.val (y : Circle L)) x) ∧
            (∀ x, χ.val x = ψ.val x - φ.val x) ∧
            (∀ k, coeff L ⟨(fun x => (φ.val x : ℂ)), complexL2Integrable L _ φ.property⟩ k =
              coeff L ⟨(fun x => (ψ.val x : ℂ)), complexL2Integrable L _ ψ.property⟩ k *
                (mollifierFT ρ (t * k / L.val) : ℂ)) ∧
            (∀ k, coeff L ⟨(fun x => (χ.val x : ℂ)), complexL2Integrable L _ χ.property⟩ k =
              coeff L ⟨(fun x => (ψ.val x : ℂ)), complexL2Integrable L _ ψ.property⟩ k -
              coeff L ⟨(fun x => (φ.val x : ℂ)), complexL2Integrable L _ φ.property⟩ k) ∧
            ∀ v, (v = φ ∨ v = χ) →
              Continuous v.val ∧ (∀ x, |v.val x| ≤ C) ∧
              ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x : ℝ,
                |circleMollify ρ L.val h (fun y : ℝ => v.val (y : Circle L)) x| ≤ C ∧
                |deriv (circleMollify ρ L.val h (fun y : ℝ => v.val (y : Circle L))) x| ≤
                  C * (1 + ∑ j, max (dist (x : Circle L) (marks j : Circle L)) h ^ (-1 + P.val.2 - α')) ∧
                |deriv (deriv (circleMollify ρ L.val h (fun y : ℝ => v.val (y : Circle L)))) x| ≤
                  C * (1 + ∑ j, max (dist (x : Circle L) (marks j : Circle L)) h ^ (-2 + P.val.2 - α')) := by
  obtain ⟨K, hK, htransport⟩ := compact_regTransportBounds P p hp η B n marks α α' C₀
    hη hB hC₀ hα0 hα1 hα' hα'0 hα'1
  obtain ⟨C, hC, hfamily⟩ := Internal.transport_family_envelopes hρ n marks
    (b := 1 - P.val.2 + α') (K := K) (by linarith) (by linarith [P.property.2.1]) hK.le
  refine ⟨C, hC, fun ell hell hdata a hprim hreg => ?_⟩
  obtain ⟨ψ, hc, hψ, hcoeff, hi, hAC, hsup, hpoint, _⟩ := htransport ell hell hdata a hprim hreg
  refine ⟨⟨ψ, hψ⟩, hc, hcoeff, ?_⟩
  have hnorm : 0 ≤ ∫ t in (-(observationLength a).val / 2)..((observationLength a).val / 2),
      |deriv (fun y : ℝ => ψ (y : Circle (observationLength a))) t| := by
    apply intervalIntegral.integral_nonneg (by linarith [(observationLength a).property])
    intro t _; exact abs_nonneg _
  have hb := hfamily (observationLength a) ((one_le_inv₀ a.property.1).mpr a.property.2)
    ⟨ψ, hψ⟩ hc (fun x => by linarith [hsup x]) hi hAC
    (by simpa only [show -(1 - P.val.2 + α') = -1 + P.val.2 - α' by ring,
      show -1 - (1 - P.val.2 + α') = -2 + P.val.2 - α' by ring] using hpoint)
  simpa only [show -(1 - P.val.2 + α') = -1 + P.val.2 - α' by ring,
    show -1 - (1 - P.val.2 + α') = -2 + P.val.2 - α' by ring] using hb

/-- Uniform near-mark and supremum bounds for the two macroscopic
transport families, including the permitted endpoint exponent increase. -/
theorem regUniform_familyTransport_macroscopic (P : Parameters) (p : Profile)
    (η B : ℝ) (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (α α' C₀ : ℝ)
    (hη : 0 < η) (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀)
    (hα0 : P.val.2 - 1 ≤ α) (hα1 : α < P.val.2 / 2) (hα' : α ≤ α')
    (hα'0 : P.val.2 - 1 < α') (hα'1 : α' < P.val.2 / 2)
    (hprim : PrimitiveRegularity unitLength η P.val.2 B ⟨p.val, p.property⟩)
    (hreg : TransportRegularity P unitLength ⟨p.val, p.property⟩ n marks α C₀)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) :
    ∃ C : ℝ, 0 < C ∧
      let L := unitLength
      ∃ ψ : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)},
        Continuous ψ.val ∧
        (∀ k, coeff L ⟨(fun x => (ψ.val x : ℂ)), complexL2Integrable L _ ψ.property⟩ k =
          transportCoeffs P L ⟨p.val, p.property⟩ k) ∧
        ∀ t : ℝ, 0 < t → t ≤ 1 →
          ∃ φ χ : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)},
            (∀ x : ℝ, φ.val (x : Circle L) = circleMollify ρ L.val t
              (fun y : ℝ => ψ.val (y : Circle L)) x) ∧
            (∀ x, χ.val x = ψ.val x - φ.val x) ∧
            (∀ k, coeff L ⟨(fun x => (φ.val x : ℂ)), complexL2Integrable L _ φ.property⟩ k =
              coeff L ⟨(fun x => (ψ.val x : ℂ)), complexL2Integrable L _ ψ.property⟩ k *
                (mollifierFT ρ (t * k / L.val) : ℂ)) ∧
            (∀ k, coeff L ⟨(fun x => (χ.val x : ℂ)), complexL2Integrable L _ χ.property⟩ k =
              coeff L ⟨(fun x => (ψ.val x : ℂ)), complexL2Integrable L _ ψ.property⟩ k -
              coeff L ⟨(fun x => (φ.val x : ℂ)), complexL2Integrable L _ φ.property⟩ k) ∧
            ∀ v, (v = φ ∨ v = χ) →
              Continuous v.val ∧ (∀ x, |v.val x| ≤ C) ∧
              ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x : ℝ,
                |circleMollify ρ L.val h (fun y : ℝ => v.val (y : Circle L)) x| ≤ C ∧
                |deriv (circleMollify ρ L.val h (fun y : ℝ => v.val (y : Circle L))) x| ≤
                  C * (1 + ∑ j, max (dist (x : Circle L) (marks j : Circle L)) h ^ (-1 + P.val.2 - α')) ∧
                |deriv (deriv (circleMollify ρ L.val h (fun y : ℝ => v.val (y : Circle L)))) x| ≤
                  C * (1 + ∑ j, max (dist (x : Circle L) (marks j : Circle L)) h ^ (-2 + P.val.2 - α')) := by
  obtain ⟨K, hK, ψ, hc, hψ, hcoeff, hi, hAC, hsup, hpoint⟩ := macroscopic_regTransportBounds
    P p η B n marks α α' C₀ hη hB hC₀ hα0 hα1 hα' hα'0 hprim hreg
  obtain ⟨C, hC, hfamily⟩ := Internal.transport_family_envelopes hρ n marks
    (b := 1 - P.val.2 + α') (K := K) (by linarith) (by linarith [P.property.2.1]) hK.le
  refine ⟨C, hC, ⟨ψ, hψ⟩, hc, hcoeff, ?_⟩
  have hnorm : 0 ≤ ∫ t in (0 : ℝ)..1,
      |deriv (fun y : ℝ => ψ (y : Circle unitLength)) t| := by
    apply intervalIntegral.integral_nonneg (by norm_num [unitLength])
    intro t _; exact abs_nonneg _
  have hb := hfamily unitLength (by norm_num [unitLength]) ⟨ψ, hψ⟩ hc
    (fun x => by linarith [hsup x]) hi hAC
    (by simpa only [show -(1 - P.val.2 + α') = -1 + P.val.2 - α' by ring,
      show -1 - (1 - P.val.2 + α') = -2 + P.val.2 - α' by ring] using hpoint)
  simpa only [show -(1 - P.val.2 + α') = -1 + P.val.2 - α' by ring,
    show -1 - (1 - P.val.2 + α') = -2 + P.val.2 - α' by ring] using hb

end Riesz1
