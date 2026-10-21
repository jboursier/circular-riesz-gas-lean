/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegUniformMacroscopic
public import Riesz1.Variance.RegUniformCompactVariance
public import Riesz1.Variance.RegUniformDerivatives
public import Riesz1.Variance.RegUniformTransport
public import Riesz1.Variance.RegUniformFirstTransport
public import Riesz1.Variance.RegUniformSecondTransport
public import Riesz1.Variance.RegUniformTails
public import Riesz1.Variance.RegUniformAdmissibilityMacro
public import Riesz1.Variance.RegUniformAdmissibilityCompact
public import Riesz1.Variance.RegUniformCompactCompatibility
public import Riesz1.Variance.RegUniformFamilyRatesMacro
public import Riesz1.Variance.RegUniformFamilyRates
public import Riesz1.Variance.RegUniformFamilyTransportBounds
public import Riesz1.Variance.RegUniformFamilyTails

/-! # Complete uniform analytic smoothing bounds

Lemma 5.1, expressed as a conjunction of its named clauses.
The first thirteen conjuncts give all original-profile estimates, fixed support
and full admissibility. The last five give the asserted uniformity over
both resulting families, including both smoothing parameters and compact tails.
Each compact constant precedes the circle length and the scale sequence.
-/

public section

open MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace Riesz1

/-- All clauses of Lemma 5.1. The conjunction retains
the full signatures of the theorems for the named clauses, including all fixed
quantitative data, endpoint conventions and order of quantification. -/
theorem regUniform_complete :
  (∀ (P : Parameters) (p : Profile)
    (η B : ℝ) (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (α C₀ ε : ℝ)
    (_hη : 0 < η) (_hB : 0 ≤ B) (_hC₀ : 0 ≤ C₀)
    (_hα0 : P.val.2 - 1 ≤ α) (_hα1 : α < P.val.2 / 2) (_hε : 0 < ε)
    (_hprim : PrimitiveRegularity unitLength η P.val.2 B ⟨p.val, p.property⟩)
    (_hreg : TransportRegularity P unitLength ⟨p.val, p.property⟩ n marks α C₀)
    (ρ : ℝ → ℝ) (_hρ : IsMollifier ρ),
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∃ g e : Profile, ContDiff ℝ ∞ (fun x : ℝ => g.val (x : UnitAddCircle)) ∧
        (∀ x : ℝ, g.val (x : UnitAddCircle) =
          circleMollify ρ 1 h (fun t : ℝ => p.val (t : UnitAddCircle)) x) ∧
        (∀ x, e.val x = p.val x - g.val x) ∧
        circleVariance P e ⟨1, by norm_num⟩ < ⊤ ∧
        Real.sqrt (circleVariance P e ⟨1, by norm_num⟩).toReal ≤
          C * h ^ (P.val.2 / 2 - α - ε)) ∧
  (∀ (P : Parameters) (p : Profile) (hp : CompactProfile p)
    (η B : ℝ) (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (α C₀ ε : ℝ)
    (_hη : 0 < η) (_hB : 0 ≤ B) (_hC₀ : 0 ≤ C₀)
    (_hα0 : P.val.2 - 1 ≤ α) (_hα1 : α < P.val.2 / 2) (_hε : 0 < ε)
    (ρ : ℝ → ℝ) (_hρ : IsMollifier ρ),
    ∃ C : ℝ, 0 < C ∧ ∀ ell : Scales,
      Tendsto (fun k : ℕ => (ell ⟨k + 1, Nat.succ_pos k⟩).val) atTop (𝓝 0) →
      (∀ N, PrimitiveRegularity (observationLength (ell N)) η P.val.2 B
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ ∧
        TransportRegularity P (observationLength (ell N))
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩
            n marks α C₀) →
      ∀ (a : Scale) (h : ℝ), 0 < h → h ≤ 1 →
        ∃ g e : Profile, ContDiff ℝ ∞ (fun x : ℝ => g.val (x : UnitAddCircle)) ∧
          (∀ x : ℝ, g.val (x : UnitAddCircle) =
            circleMollify ρ 1 (h / (observationLength a).val)
              (fun t : ℝ => testAtScale p a (t : UnitAddCircle)) x) ∧
          (∀ x : ℝ, g.val (x : UnitAddCircle) =
            circleMollify ρ (observationLength a).val h
              (fun t : ℝ => periodizedProfile p (observationLength a)
                (t : Circle (observationLength a))) ((observationLength a).val * x)) ∧
          (∀ x, e.val x = testAtScale p a x - g.val x) ∧
          ENNReal.ofReal (a.val ^ (-P.val.2)) * circleVariance P e ⟨1, by norm_num⟩ < ⊤ ∧
          Real.sqrt (ENNReal.ofReal (a.val ^ (-P.val.2)) *
            circleVariance P e ⟨1, by norm_num⟩).toReal ≤
              C * h ^ (P.val.2 / 2 - α - ε)) ∧
  (∀ (P : Parameters) (p : Profile)
    (η B : ℝ) (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (α C₀ ε : ℝ)
    (_hη : 0 < η) (_hB : 0 ≤ B) (_hC₀ : 0 ≤ C₀)
    (_hα0 : P.val.2 - 1 ≤ α) (_hα1 : α < P.val.2 / 2) (_hε : 0 < ε)
    (_hprim : PrimitiveRegularity unitLength η P.val.2 B ⟨p.val, p.property⟩)
    (_hreg : TransportRegularity P unitLength ⟨p.val, p.property⟩ n marks α C₀)
    (ρ : ℝ → ℝ) (_hρ : IsMollifier ρ),
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∃ ph : Profile, Continuous ph.val ∧
        ContDiff ℝ ∞ (fun x : ℝ => ph.val (x : UnitAddCircle)) ∧
        (∀ x : ℝ, ph.val (x : UnitAddCircle) = circleMollify ρ 1 h
          (fun t : ℝ => p.val (t : UnitAddCircle)) x) ∧
        (∀ x : ℝ, |deriv (fun t : ℝ => ph.val (t : UnitAddCircle)) x| ≤
          C * h ^ (-1 - α - ε)) ∧
        ∀ x : ℝ, |deriv (deriv (fun t : ℝ => ph.val (t : UnitAddCircle))) x| ≤
          C * h ^ (-2 - α - ε)) ∧
  (∀ (P : Parameters) (p : Profile) (hp : CompactProfile p)
    (η B : ℝ) (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (α C₀ ε : ℝ)
    (_hη : 0 < η) (_hB : 0 ≤ B) (_hC₀ : 0 ≤ C₀)
    (_hα0 : P.val.2 - 1 ≤ α) (_hα1 : α < P.val.2 / 2) (_hε : 0 < ε)
    (ρ : ℝ → ℝ) (_hρ : IsMollifier ρ),
    ∃ C : ℝ, 0 < C ∧ ∀ ell : Scales,
      Tendsto (fun k : ℕ => (ell ⟨k + 1, Nat.succ_pos k⟩).val) atTop (𝓝 0) →
      (∀ N, PrimitiveRegularity (observationLength (ell N)) η P.val.2 B
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ ∧
        TransportRegularity P (observationLength (ell N))
          ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩
            n marks α C₀) →
      ∀ (a : Scale) (h : ℝ), 0 < h → h ≤ 1 →
        ∃ ph : {f : Circle (observationLength a) → ℝ //
            MemLp (fun x => (f x : ℂ)) 2 (arclength (observationLength a))},
          Continuous ph.val ∧
          ContDiff ℝ ∞ (fun x : ℝ => ph.val (x : Circle (observationLength a))) ∧
          (∀ x : ℝ, ph.val (x : Circle (observationLength a)) =
            circleMollify ρ (observationLength a).val h
              (fun t : ℝ => periodizedProfile p (observationLength a)
                (t : Circle (observationLength a))) x) ∧
          (∀ x : ℝ, |deriv (fun t : ℝ => ph.val (t : Circle (observationLength a))) x| ≤
            C * h ^ (-1 - α - ε)) ∧
          ∀ x : ℝ, |deriv (deriv (fun t : ℝ => ph.val (t : Circle (observationLength a)))) x| ≤
            C * h ^ (-2 - α - ε)) ∧
  (∀ (P : Parameters) (η B : ℝ)
    (_hη : 0 < η) (_hB : 0 ≤ B),
    ∃ C : ℝ, 0 < C ∧ ∀ (L : Length)
      (f : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)}),
      PrimitiveRegularity L η P.val.2 B f →
      ∃ ψ : {g : Circle L → ℝ // MemLp (fun x => (g x : ℂ)) 2 (arclength L)},
        Continuous ψ.val ∧
        (∀ k : ℤ, coeff L ⟨(fun x => (ψ.val x : ℂ)),
          complexL2Integrable L _ ψ.property⟩ k = transportCoeffs P L f k) ∧
        ∀ (ρ : ℝ → ℝ), IsMollifier ρ → ∀ h : ℝ, 0 < h →
          ∃ g ψh : {g : Circle L → ℝ // MemLp (fun x => (g x : ℂ)) 2 (arclength L)},
            (∀ x : ℝ, g.val (x : Circle L) =
              circleMollify ρ L.val h (fun t : ℝ => f.val (t : Circle L)) x) ∧
            (∀ x : ℝ, ψh.val (x : Circle L) =
              circleMollify ρ L.val h (fun t : ℝ => ψ.val (t : Circle L)) x) ∧
            ContDiff ℝ ∞ (fun t : ℝ => ψh.val (t : Circle L)) ∧
            (∀ k : ℤ, coeff L ⟨(fun x => (ψh.val x : ℂ)),
              complexL2Integrable L _ ψh.property⟩ k = transportCoeffs P L g k) ∧
            ∀ x : Circle L, |ψh.val x| ≤ C) ∧
  (∀ (P : Parameters) (p : Profile)
    (η B : ℝ) (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (α α' C₀ : ℝ)
    (_hη : 0 < η) (_hB : 0 ≤ B) (_hC₀ : 0 ≤ C₀)
    (_hα0 : P.val.2 - 1 ≤ α) (_hα1 : α < P.val.2 / 2) (_hα' : α ≤ α')
    (_hα'0 : P.val.2 - 1 < α') (_hα'1 : α' < P.val.2 / 2)
    (_hprim : PrimitiveRegularity unitLength η P.val.2 B ⟨p.val, p.property⟩)
    (_hreg : TransportRegularity P unitLength ⟨p.val, p.property⟩ n marks α C₀)
    (ρ : ℝ → ℝ) (_hρ : IsMollifier ρ),
    ∃ C : ℝ, 0 < C ∧ ∃ ψ : Circle unitLength → ℝ, Continuous ψ ∧
      ∃ hψ : MemLp (fun x => (ψ x : ℂ)) 2 (arclength unitLength),
        (∀ k : ℤ, coeff unitLength ⟨(fun x => (ψ x : ℂ)), complexL2Integrable _ _ hψ⟩ k =
          transportCoeffs P unitLength ⟨p.val, p.property⟩ k) ∧
        ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x : ℝ,
          |deriv (circleMollify ρ 1 h (fun t : ℝ => ψ (t : Circle unitLength))) x| ≤
            C * (1 + ∑ j, max (dist (x : Circle unitLength) (marks j : Circle unitLength)) h ^
              (-1 + P.val.2 - α'))) ∧
  (∀ (P : Parameters)
    (p : Profile) (hp : CompactProfile p) (η B : ℝ)
    (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (α α' C₀ : ℝ)
    (_hη : 0 < η) (_hB : 0 ≤ B) (_hC₀ : 0 ≤ C₀)
    (_hα0 : P.val.2 - 1 ≤ α) (_hα1 : α < P.val.2 / 2) (_hα' : α ≤ α')
    (_hα'0 : P.val.2 - 1 < α') (_hα'1 : α' < P.val.2 / 2)
    (ρ : ℝ → ℝ) (_hρ : IsMollifier ρ),
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
        ∃ ψ : Circle (observationLength a) → ℝ, Continuous ψ ∧
          ∃ hψ : MemLp (fun x => (ψ x : ℂ)) 2 (arclength (observationLength a)),
            (∀ k : ℤ, coeff (observationLength a) ⟨(fun x => (ψ x : ℂ)),
                complexL2Integrable _ _ hψ⟩ k = transportCoeffs P (observationLength a)
                  ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ k) ∧
            ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x : ℝ,
              |deriv (circleMollify ρ (observationLength a).val h
                (fun t : ℝ => ψ (t : Circle (observationLength a)))) x| ≤
                C * (1 + ∑ j, max (dist (x : Circle (observationLength a))
                  (marks j : Circle (observationLength a))) h ^ (-1 + P.val.2 - α'))) ∧
  (∀ (P : Parameters) (p : Profile)
    (η B : ℝ) (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (α α' C₀ : ℝ)
    (_hη : 0 < η) (_hB : 0 ≤ B) (_hC₀ : 0 ≤ C₀)
    (_hα0 : P.val.2 - 1 ≤ α) (_hα1 : α < P.val.2 / 2) (_hα' : α ≤ α')
    (_hα'0 : P.val.2 - 1 < α') (_hα'1 : α' < P.val.2 / 2)
    (_hprim : PrimitiveRegularity unitLength η P.val.2 B ⟨p.val, p.property⟩)
    (_hreg : TransportRegularity P unitLength ⟨p.val, p.property⟩ n marks α C₀)
    (ρ : ℝ → ℝ) (_hρ : IsMollifier ρ),
    ∃ C : ℝ, 0 < C ∧ ∃ ψ : Circle unitLength → ℝ, Continuous ψ ∧
      ∃ hψ : MemLp (fun x => (ψ x : ℂ)) 2 (arclength unitLength),
        (∀ k : ℤ, coeff unitLength ⟨(fun x => (ψ x : ℂ)), complexL2Integrable _ _ hψ⟩ k =
          transportCoeffs P unitLength ⟨p.val, p.property⟩ k) ∧
        ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x : ℝ,
          |deriv (deriv (circleMollify ρ 1 h (fun t : ℝ => ψ (t : Circle unitLength)))) x| ≤
            C * (1 + ∑ j, max (dist (x : Circle unitLength) (marks j : Circle unitLength)) h ^
              (-2 + P.val.2 - α'))) ∧
  (∀ (P : Parameters)
    (p : Profile) (hp : CompactProfile p) (η B : ℝ)
    (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (α α' C₀ : ℝ)
    (_hη : 0 < η) (_hB : 0 ≤ B) (_hC₀ : 0 ≤ C₀)
    (_hα0 : P.val.2 - 1 ≤ α) (_hα1 : α < P.val.2 / 2) (_hα' : α ≤ α')
    (_hα'0 : P.val.2 - 1 < α') (_hα'1 : α' < P.val.2 / 2)
    (ρ : ℝ → ℝ) (_hρ : IsMollifier ρ),
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
        ∃ ψ : Circle (observationLength a) → ℝ, Continuous ψ ∧
          ∃ hψ : MemLp (fun x => (ψ x : ℂ)) 2 (arclength (observationLength a)),
            (∀ k : ℤ, coeff (observationLength a) ⟨(fun x => (ψ x : ℂ)),
                complexL2Integrable _ _ hψ⟩ k = transportCoeffs P (observationLength a)
                  ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ k) ∧
            ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x : ℝ,
              |deriv (deriv (circleMollify ρ (observationLength a).val h
                (fun t : ℝ => ψ (t : Circle (observationLength a))))) x| ≤
                C * (1 + ∑ j, max (dist (x : Circle (observationLength a))
                  (marks j : Circle (observationLength a))) h ^ (-2 + P.val.2 - α'))) ∧
  (∀ (P : Parameters)
    (p : Profile) (hp : CompactProfile p) (η B : ℝ)
    (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (α α' C₀ : ℝ)
    (_hη : 0 < η) (_hB : 0 ≤ B) (_hC₀ : 0 ≤ C₀)
    (_hα0 : P.val.2 - 1 ≤ α) (_hα1 : α < P.val.2 / 2) (_hα' : α ≤ α')
    (_hα'0 : P.val.2 - 1 < α') (_hα'1 : α' < P.val.2 / 2)
    (ρ : ℝ → ℝ) (_hρ : IsMollifier ρ),
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
        ∃ ψ : Circle (observationLength a) → ℝ, Continuous ψ ∧
          ∃ hψ : MemLp (fun x => (ψ x : ℂ)) 2 (arclength (observationLength a)),
            (∀ k : ℤ, coeff (observationLength a) ⟨(fun x => (ψ x : ℂ)),
                complexL2Integrable _ _ hψ⟩ k = transportCoeffs P (observationLength a)
                  ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ k) ∧
            ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x : ℝ,
              2 ≤ |x| → |x| ≤ (observationLength a).val / 2 →
                |deriv (circleMollify ρ (observationLength a).val h
                  (fun t : ℝ => ψ (t : Circle (observationLength a)))) x| ≤
                    C * |x| ^ (P.val.2 - 2) ∧
                |deriv (deriv (circleMollify ρ (observationLength a).val h
                  (fun t : ℝ => ψ (t : Circle (observationLength a))))) x| ≤
                    C * |x| ^ (P.val.2 - 3)) ∧
  (∀ (P : Parameters) (p : Profile)
    (η B : ℝ) (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (α α' C₀ : ℝ)
    (_hη : 0 < η) (hηs : η < P.val.2) (_hB : 0 < B) (_hC₀ : 0 ≤ C₀)
    (_hα0 : P.val.2 - 1 ≤ α) (_hα1 : α < P.val.2 / 2) (_hα' : α ≤ α')
    (_hα'0 : P.val.2 - 1 < α') (_hα'1 : α' < P.val.2 / 2)
    (_hprim : PrimitiveRegularity unitLength η P.val.2 B ⟨p.val, p.property⟩)
    (_hreg : TransportRegularity P unitLength ⟨p.val, p.property⟩ n marks α C₀)
    (ρ : ℝ → ℝ) (_hρ : IsMollifier ρ),
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      ∃ g e : Profile,
        (∀ x : ℝ, g.val (x : Circle unitLength) =
          circleMollify ρ 1 h (fun t : ℝ => p.val (t : Circle unitLength)) x) ∧
        (∀ x, e.val x = p.val x - g.val x) ∧
        ∀ ell : Scales, (∀ N, (ell N).val = 1) →
          Admissible P g ell α' (η, B, C, ⟨n, marks⟩) ∧
          Admissible P e ell α' (η, 2 * B, C, ⟨n, marks⟩)) ∧
  (∀ (P : Parameters) (p : Profile)
    (hp : CompactProfile p) (η B : ℝ) (n : ℕ+) (marks : Fin (n : ℕ) → ℝ)
    (α α' C₀ : ℝ) (_hη : 0 < η) (hηs : η < P.val.2)
    (_hB : 0 < B) (_hC₀ : 0 ≤ C₀)
    (_hα0 : P.val.2 - 1 ≤ α) (_hα1 : α < P.val.2 / 2) (_hα' : α ≤ α')
    (_hα'0 : P.val.2 - 1 < α') (_hα'1 : α' < P.val.2 / 2)
    (ρ : ℝ → ℝ) (_hρ : IsMollifier ρ),
    ∃ C h₀ r : ℝ, 0 < C ∧ 0 < h₀ ∧ h₀ ≤ 1 ∧ 0 < r ∧ r < 1 / 2 ∧
      ∀ ell : Scales,
        Tendsto (fun k : ℕ => (ell ⟨k + 1, Nat.succ_pos k⟩).val) atTop (𝓝 0) →
        (∀ N, PrimitiveRegularity (observationLength (ell N)) η P.val.2 B
            ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ ∧
          TransportRegularity P (observationLength (ell N))
            ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩
              n marks α C₀) →
        ∀ h : ℝ, 0 < h → h ≤ h₀ → ∃ g e : Profile,
          (∀ x : ℝ, g.val (x : Circle unitLength) =
            circleMollify ρ 1 h (fun t : ℝ => p.val (t : Circle unitLength)) x) ∧
          (∀ x, e.val x = p.val x - g.val x) ∧
          (∀ x : ℝ, r ≤ |x| → zeroExtension g x = 0) ∧
          (∀ᵐ x : ℝ, r ≤ |x| → zeroExtension e x = 0) ∧
          Admissible P g ell α' (η, B, C, ⟨n, marks⟩) ∧
          Admissible P e ell α' (η, 2 * B, C, ⟨n, marks⟩)) ∧
  (∀ (p : Profile) (hp : CompactProfile p)
    (ρ : ℝ → ℝ) (_hρ : IsMollifier ρ),
    ∃ h₀ r : ℝ, 0 < h₀ ∧ 0 < r ∧ r < 1 / 2 ∧
      ∀ h : ℝ, 0 < h → h ≤ h₀ →
        ∃ g e : Profile,
          ContDiff ℝ ∞ (fun x : ℝ => g.val (x : Circle unitLength)) ∧
          (∀ x : ℝ, g.val (x : Circle unitLength) =
            circleMollify ρ 1 h (fun t : ℝ => p.val (t : Circle unitLength)) x) ∧
          (∀ x, e.val x = p.val x - g.val x) ∧
          (∀ x : ℝ, r ≤ |x| → zeroExtension g x = 0) ∧
          (∀ᵐ x : ℝ, r ≤ |x| → zeroExtension e x = 0) ∧
          CompactProfile g ∧ CompactProfile e ∧
          ∀ a : Scale, ∀ x : ℝ,
            periodizedProfile g (observationLength a) (x : Circle (observationLength a)) =
              circleMollify ρ (observationLength a).val h
                (fun t : ℝ => periodizedProfile p (observationLength a)
                  (t : Circle (observationLength a))) x ∧
            periodizedProfile e (observationLength a) (x : Circle (observationLength a)) =
              periodizedProfile p (observationLength a) (x : Circle (observationLength a)) -
                circleMollify ρ (observationLength a).val h
                  (fun t : ℝ => periodizedProfile p (observationLength a)
                    (t : Circle (observationLength a))) x) ∧
  (∀ (P : Parameters) (p : Profile)
    (η B : ℝ) (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (α C₀ ε : ℝ)
    (_hη : 0 < η) (_hB : 0 ≤ B) (_hC₀ : 0 ≤ C₀)
    (_hα0 : P.val.2 - 1 ≤ α) (_hα1 : α < P.val.2 / 2) (_hε : 0 < ε)
    (_hprim : PrimitiveRegularity unitLength η P.val.2 B ⟨p.val, p.property⟩)
    (_hreg : TransportRegularity P unitLength ⟨p.val, p.property⟩ n marks α C₀)
    (ρ : ℝ → ℝ) (_hρ : IsMollifier ρ),
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → ∃ g e : Profile,
      (∀ x : ℝ, g.val (x : UnitAddCircle) = circleMollify ρ 1 t
        (fun y : ℝ => p.val (y : UnitAddCircle)) x) ∧
      (∀ x, e.val x = p.val x - g.val x) ∧
      ∀ v : Profile, (v = g ∨ v = e) → ∀ h : ℝ, 0 < h → h ≤ 1 →
        ∃ q d : Profile,
          ContDiff ℝ ∞ (fun x : ℝ => q.val (x : UnitAddCircle)) ∧
          (∀ x : ℝ, q.val (x : UnitAddCircle) = circleMollify ρ 1 h
            (fun y : ℝ => v.val (y : UnitAddCircle)) x) ∧
          (∀ x, d.val x = v.val x - q.val x) ∧
          circleVariance P d ⟨1, by norm_num⟩ < ⊤ ∧
          Real.sqrt (circleVariance P d ⟨1, by norm_num⟩).toReal ≤
            C * h ^ (P.val.2 / 2 - α - ε) ∧
          ∀ x : ℝ,
            |deriv (circleMollify ρ 1 h (fun y : ℝ => v.val (y : UnitAddCircle))) x| ≤
              C * h ^ (-1 - α - ε) ∧
            |deriv (deriv (circleMollify ρ 1 h (fun y : ℝ => v.val (y : UnitAddCircle)))) x| ≤
              C * h ^ (-2 - α - ε)) ∧
  (∀ (P : Parameters) (p : Profile)
    (hp : CompactProfile p) (η B : ℝ) (n : ℕ+) (marks : Fin (n : ℕ) → ℝ)
    (α C₀ ε : ℝ) (_hη : 0 < η) (_hB : 0 ≤ B) (_hC₀ : 0 ≤ C₀)
    (_hα0 : P.val.2 - 1 ≤ α) (_hα1 : α < P.val.2 / 2) (_hε : 0 < ε)
    (ρ : ℝ → ℝ) (_hρ : IsMollifier ρ),
    ∃ C H r : ℝ, 0 < C ∧ 0 < H ∧ 0 < r ∧ r < 1 / 2 ∧
      ∀ ell : Scales,
        Tendsto (fun k : ℕ => (ell ⟨k + 1, Nat.succ_pos k⟩).val) atTop (𝓝 0) →
        (∀ N, PrimitiveRegularity (observationLength (ell N)) η P.val.2 B
            ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ ∧
          TransportRegularity P (observationLength (ell N))
            ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩
              n marks α C₀) →
        ∀ t : ℝ, 0 < t → t ≤ H → ∃ g e : Profile,
          (∀ x : ℝ, g.val (x : UnitAddCircle) = circleMollify ρ 1 t
            (fun y : ℝ => p.val (y : UnitAddCircle)) x) ∧
          (∀ x, e.val x = p.val x - g.val x) ∧
          (∀ x : ℝ, r ≤ |x| → zeroExtension g x = 0) ∧
          (∀ᵐ x : ℝ, r ≤ |x| → zeroExtension e x = 0) ∧
          ∀ v : Profile, (v = g ∨ v = e) → ∀ (a : Scale) (h : ℝ), 0 < h → h ≤ 1 →
            ∃ q d : Profile,
              ContDiff ℝ ∞ (fun x : ℝ => q.val (x : UnitAddCircle)) ∧
              (∀ x : ℝ, q.val (x : UnitAddCircle) = circleMollify ρ 1
                (h / (observationLength a).val) (fun y : ℝ => testAtScale v a (y : UnitAddCircle)) x) ∧
              (∀ x, d.val x = testAtScale v a x - q.val x) ∧
              ENNReal.ofReal (a.val ^ (-P.val.2)) * circleVariance P d ⟨1, by norm_num⟩ < ⊤ ∧
              Real.sqrt (ENNReal.ofReal (a.val ^ (-P.val.2)) *
                circleVariance P d ⟨1, by norm_num⟩).toReal ≤ C * h ^ (P.val.2 / 2 - α - ε) ∧
              ∀ x : ℝ,
                |deriv (circleMollify ρ (observationLength a).val h
                  (fun y : ℝ => periodizedProfile v (observationLength a) (y : Circle (observationLength a)))) x| ≤
                    C * h ^ (-1 - α - ε) ∧
                |deriv (deriv (circleMollify ρ (observationLength a).val h
                  (fun y : ℝ => periodizedProfile v (observationLength a) (y : Circle (observationLength a))))) x| ≤
                    C * h ^ (-2 - α - ε)) ∧
  (∀ (P : Parameters) (p : Profile)
    (η B : ℝ) (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (α α' C₀ : ℝ)
    (_hη : 0 < η) (_hB : 0 ≤ B) (_hC₀ : 0 ≤ C₀)
    (_hα0 : P.val.2 - 1 ≤ α) (_hα1 : α < P.val.2 / 2) (_hα' : α ≤ α')
    (_hα'0 : P.val.2 - 1 < α') (_hα'1 : α' < P.val.2 / 2)
    (_hprim : PrimitiveRegularity unitLength η P.val.2 B ⟨p.val, p.property⟩)
    (_hreg : TransportRegularity P unitLength ⟨p.val, p.property⟩ n marks α C₀)
    (ρ : ℝ → ℝ) (_hρ : IsMollifier ρ),
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
                  C * (1 + ∑ j, max (dist (x : Circle L) (marks j : Circle L)) h ^ (-2 + P.val.2 - α'))) ∧
  (∀ (P : Parameters) (p : Profile) (hp : CompactProfile p)
    (η B : ℝ) (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (α α' C₀ : ℝ)
    (_hη : 0 < η) (_hB : 0 ≤ B) (_hC₀ : 0 ≤ C₀)
    (_hα0 : P.val.2 - 1 ≤ α) (_hα1 : α < P.val.2 / 2) (_hα' : α ≤ α')
    (_hα'0 : P.val.2 - 1 < α') (_hα'1 : α' < P.val.2 / 2)
    (ρ : ℝ → ℝ) (_hρ : IsMollifier ρ),
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
                  C * (1 + ∑ j, max (dist (x : Circle L) (marks j : Circle L)) h ^ (-2 + P.val.2 - α'))) ∧
  (∀ (P : Parameters) (p : Profile)
    (hp : CompactProfile p) (η B : ℝ) (n : ℕ+) (marks : Fin (n : ℕ) → ℝ)
    (α α' C₀ : ℝ) (_hη : 0 < η) (_hB : 0 ≤ B) (_hC₀ : 0 ≤ C₀)
    (_hα0 : P.val.2 - 1 ≤ α) (_hα1 : α < P.val.2 / 2) (_hα' : α ≤ α')
    (_hα'0 : P.val.2 - 1 < α') (_hα'1 : α' < P.val.2 / 2)
    (ρ : ℝ → ℝ) (_hρ : IsMollifier ρ),
    ∃ C H r : ℝ, 0 < C ∧ 0 < H ∧ 0 < r ∧ r < 1 / 2 ∧
      ∀ ell : Scales,
        Tendsto (fun k : ℕ => (ell ⟨k + 1, Nat.succ_pos k⟩).val) atTop (𝓝 0) →
        (∀ N, PrimitiveRegularity (observationLength (ell N)) η P.val.2 B
            ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ ∧
          TransportRegularity P (observationLength (ell N))
            ⟨periodizedProfile p (observationLength (ell N)), periodizedProfileL2 p (ell N)⟩ n marks α C₀) →
        ∀ t : ℝ, 0 < t → t ≤ H → ∃ g e : Profile,
          (∀ x : ℝ, g.val (x : UnitAddCircle) = circleMollify ρ 1 t
            (fun y : ℝ => p.val (y : UnitAddCircle)) x) ∧
          (∀ x, e.val x = p.val x - g.val x) ∧
          (∀ x : ℝ, r ≤ |x| → zeroExtension g x = 0) ∧
          (∀ᵐ x : ℝ, r ≤ |x| → zeroExtension e x = 0) ∧
          ∀ v : Profile, (v = g ∨ v = e) →
            (∫ x : ℝ, |zeroExtension v x|) ≤ 2 * ∫ x : ℝ, |zeroExtension p x| ∧
            ∀ a : Scale,
              PrimitiveRegularity (observationLength a) η P.val.2 B
                ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ →
              TransportRegularity P (observationLength a)
                ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ n marks α C₀ →
              ∃ ψ : Circle (observationLength a) → ℝ, Continuous ψ ∧
                ∃ hψ : MemLp (fun x => (ψ x : ℂ)) 2 (arclength (observationLength a)),
                  (∀ k, coeff (observationLength a) ⟨(fun x => (ψ x : ℂ)), complexL2Integrable _ _ hψ⟩ k =
                    transportCoeffs P (observationLength a)
                      ⟨periodizedProfile v (observationLength a), periodizedProfileL2 v a⟩ k) ∧
                  ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x : ℝ,
                    2 ≤ dist (x : Circle (observationLength a)) 0 →
                    |deriv (circleMollify ρ (observationLength a).val h
                      (fun y : ℝ => ψ (y : Circle (observationLength a)))) x| ≤
                        C * dist (x : Circle (observationLength a)) 0 ^ (P.val.2 - 2) ∧
                    |deriv (deriv (circleMollify ρ (observationLength a).val h
                      (fun y : ℝ => ψ (y : Circle (observationLength a))))) x| ≤
                        C * dist (x : Circle (observationLength a)) 0 ^ (P.val.2 - 3)) := by
  exact ⟨regUniform_variance_macroscopic,
    regUniform_variance_compact,
    regUniform_derivatives_macroscopic,
    regUniform_derivatives_compact,
    regUniform_smoothed_transport,
    regUniform_firstTransport_macroscopic,
    regUniform_firstTransport_compact,
    regUniform_secondTransport_macroscopic,
    regUniform_secondTransport_compact,
    regUniform_transportTails_compact,
    regUniform_admissible_macroscopic,
    regUniform_admissible_compact,
    regUniform_compactCompatibility,
    regUniform_familyRates_macroscopic,
    regUniform_familyRates_compact,
    regUniform_familyTransport_macroscopic,
    regUniform_familyTransport_compact,
    regUniform_familyTails_compact⟩

end Riesz1
