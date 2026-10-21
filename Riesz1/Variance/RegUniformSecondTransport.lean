/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.ToMathlib.FiniteMarkMollifyDerivative
public import Riesz1.ToMathlib.CircleMollifyWeakDerivative
public import Riesz1.Variance.RegTransportBoundsFixedCircle
public import Riesz1.Variance.RegTransportBoundsCompact

/-!
# The second smoothed transport derivative at finitely many marks

Lemma 5.1: the exact `max(distance,h)` envelope,
including the endpoint convention and constants before every compact circle.
The smoothed transport is the convolution of the continuous transport.
-/

public section

open MeasureTheory Filter
open scoped ContDiff Topology

namespace Riesz1
namespace Internal

/-- Smooth the locally integrable first derivative, using the original
second derivative only on windows avoiding every marked point. -/
theorem smoothed_transport_second_of_capped_bound {ρ : ℝ → ℝ} (hρ : IsMollifier ρ)
    {b : ℝ} (hb : 0 ≤ b) (hb1 : b < 1) :
    ∃ D : ℝ, 0 < D ∧ ∀ (L : Length), 1 ≤ L.val →
      ∀ (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (C : ℝ), 0 ≤ C →
      ∀ ψ : Circle L → ℝ, Continuous ψ →
      LocallyIntegrable (deriv (fun t : ℝ => ψ (t : Circle L))) volume →
      (∀ u v : ℝ, AbsolutelyContinuousOnInterval (fun t : ℝ => ψ (t : Circle L)) u v) →
      (∀ x : ℝ, (∀ j, (x : Circle L) ≠ (marks j : Circle L)) →
        ContDiffAt ℝ 2 (fun t : ℝ => ψ (t : Circle L)) x ∧
        |deriv (fun t : ℝ => ψ (t : Circle L)) x| ≤ C *
          cappedMarkDistance (fun j => (marks j : Circle L)) (x : Circle L) ^ (-b) ∧
        |deriv (deriv (fun t : ℝ => ψ (t : Circle L))) x| ≤ C *
          cappedMarkDistance (fun j => (marks j : Circle L)) (x : Circle L) ^ (-1 - b)) →
      ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x : ℝ,
        |deriv (deriv (circleMollify ρ L.val h (fun t : ℝ => ψ (t : Circle L)))) x| ≤
          D * C * ((n : ℕ) + 1) *
            (1 + ∑ j, max (dist (x : Circle L) (marks j : Circle L)) h ^ (-1 - b)) := by
  obtain ⟨D, hD, hfinite⟩ := circleMollify_finiteMark_deriv_bound hρ hb hb1
  refine ⟨D, hD, fun L hL n marks C hC ψ hc hi hAC hpoint h hh hh1 x => ?_⟩
  have : Fact (0 < L.val) := ⟨L.property⟩
  let F := fun t : ℝ => ψ (t : Circle L)
  have hp : Function.Periodic F L.val := by intro t; simp only [F, AddCircle.coe_add_period]
  have hmajor : ∀ᵐ y : ℝ, |deriv F y| ≤ C *
      (1 + ∑ j, dist (y : Circle L) (marks j : Circle L) ^ (-b)) := by
    filter_upwards [(CircleSingularity.countable_marked_lifts (T := L.val) marks).ae_notMem volume]
      with y hy
    have hne : ∀ j, (y : Circle L) ≠ (marks j : Circle L) := by
      intro j he
      exact hy ⟨j, he⟩
    exact ((hpoint y hne).2.1).trans (mul_le_mul_of_nonneg_left
      (cappedMarkDistance_rpow_le_one_add_sum _ _ _) hC)
  have hFc : Continuous F := hc.comp (AddCircle.continuous_mk' L.val)
  have heq : deriv (circleMollify ρ L.val h F) = circleMollify ρ L.val h (deriv F) :=
    funext (deriv_circleMollify_of_absolutelyContinuous hρ L.property hh hFc hp hAC)
  change |deriv (deriv (circleMollify ρ L.val h F)) x| ≤ _
  rw [heq]
  have hd (y : ℝ) (hy : ∀ j, (y : Circle L) ≠ (marks j : Circle L)) :
      DifferentiableAt ℝ (deriv F) y ∧ |deriv (deriv F) y| ≤
        C * cappedMarkDistance (fun j => (marks j : Circle L)) (y : Circle L) ^ (-1 - b) :=
    ⟨((hpoint y hy).1.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num),
      (hpoint y hy).2.2⟩
  simpa only [Fintype.card_fin] using
    hfinite L.val hL marks C hC (deriv F) (Riesz1.periodic_deriv hp) hi hmajor hd h hh hh1 x

end Internal

/-- The second near-mark envelope of Lemma 5.1 on the macroscopic
circle. Use `α' = α` in the strict case, and any permitted `α' = α + δ`
at the endpoint. The representative has the transport coefficients. -/
theorem regUniform_secondTransport_macroscopic (P : Parameters) (p : Profile)
    (η B : ℝ) (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (α α' C₀ : ℝ)
    (hη : 0 < η) (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀)
    (hα0 : P.val.2 - 1 ≤ α) (hα1 : α < P.val.2 / 2) (hα' : α ≤ α')
    (hα'0 : P.val.2 - 1 < α') (hα'1 : α' < P.val.2 / 2)
    (hprim : PrimitiveRegularity unitLength η P.val.2 B ⟨p.val, p.property⟩)
    (hreg : TransportRegularity P unitLength ⟨p.val, p.property⟩ n marks α C₀)
    (ρ : ℝ → ℝ) (hρ : IsMollifier ρ) :
    ∃ C : ℝ, 0 < C ∧ ∃ ψ : Circle unitLength → ℝ, Continuous ψ ∧
      ∃ hψ : MemLp (fun x => (ψ x : ℂ)) 2 (arclength unitLength),
        (∀ k : ℤ, coeff unitLength ⟨(fun x => (ψ x : ℂ)), complexL2Integrable _ _ hψ⟩ k =
          transportCoeffs P unitLength ⟨p.val, p.property⟩ k) ∧
        ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x : ℝ,
          |deriv (deriv (circleMollify ρ 1 h (fun t : ℝ => ψ (t : Circle unitLength)))) x| ≤
            C * (1 + ∑ j, max (dist (x : Circle unitLength) (marks j : Circle unitLength)) h ^
              (-2 + P.val.2 - α')) := by
  obtain ⟨K, hK, ψ, hc, hψ, hcoeff, hi, hAC, _, hpoint⟩ := macroscopic_regTransportBounds
    P p η B n marks α α' C₀ hη hB hC₀ hα0 hα1 hα' hα'0 hprim hreg
  obtain ⟨D, hD, hb⟩ := Internal.smoothed_transport_second_of_capped_bound hρ
    (b := 1 - P.val.2 + α') (by linarith) (by linarith [P.property.2.1])
  refine ⟨D * K * ((n : ℕ) + 1), by positivity, ψ, hc, hψ, hcoeff, fun h hh hh1 x => ?_⟩
  have hp := hb unitLength (by norm_num [unitLength]) n marks K hK.le ψ hc hi hAC
    (by simpa only [show -(1 - P.val.2 + α') = -1 + P.val.2 - α' by ring,
      show -1 - (1 - P.val.2 + α') = -2 + P.val.2 - α' by ring] using hpoint) h hh hh1 x
  simpa only [show -1 - (1 - P.val.2 + α') = -2 + P.val.2 - α' by ring, unitLength] using hp

/-- The second near-mark envelope of Lemma 5.1 for compact profiles.
Its constant precedes the witnessing sequence, circle and radius. The same
exponent parameters cover the strict case and the endpoint convention. -/
theorem regUniform_secondTransport_compact (P : Parameters)
    (p : Profile) (hp : CompactProfile p) (η B : ℝ)
    (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (α α' C₀ : ℝ)
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
        ∃ ψ : Circle (observationLength a) → ℝ, Continuous ψ ∧
          ∃ hψ : MemLp (fun x => (ψ x : ℂ)) 2 (arclength (observationLength a)),
            (∀ k : ℤ, coeff (observationLength a) ⟨(fun x => (ψ x : ℂ)),
                complexL2Integrable _ _ hψ⟩ k = transportCoeffs P (observationLength a)
                  ⟨periodizedProfile p (observationLength a), periodizedProfileL2 p a⟩ k) ∧
            ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ x : ℝ,
              |deriv (deriv (circleMollify ρ (observationLength a).val h
                (fun t : ℝ => ψ (t : Circle (observationLength a))))) x| ≤
                C * (1 + ∑ j, max (dist (x : Circle (observationLength a))
                  (marks j : Circle (observationLength a))) h ^ (-2 + P.val.2 - α')) := by
  obtain ⟨K, hK, htransport⟩ := compact_regTransportBounds P p hp η B n marks α α' C₀
    hη hB hC₀ hα0 hα1 hα' hα'0 hα'1
  obtain ⟨D, hD, hb⟩ := Internal.smoothed_transport_second_of_capped_bound hρ
    (b := 1 - P.val.2 + α') (by linarith) (by linarith [P.property.2.1])
  refine ⟨D * K * ((n : ℕ) + 1), by positivity, fun ell hell hfamily a hprim hreg => ?_⟩
  obtain ⟨ψ, hc, hψ, hcoeff, hi, hAC, _, hpoint, _⟩ := htransport ell hell hfamily a hprim hreg
  refine ⟨ψ, hc, hψ, hcoeff, fun h hh hh1 x => ?_⟩
  have hL : 1 ≤ (observationLength a).val := (one_le_inv₀ a.property.1).mpr a.property.2
  have hbnd := hb (observationLength a) hL n marks K hK.le ψ hc hi hAC
    (by simpa only [show -(1 - P.val.2 + α') = -1 + P.val.2 - α' by ring,
      show -1 - (1 - P.val.2 + α') = -2 + P.val.2 - α' by ring] using hpoint) h hh hh1 x
  simpa only [show -1 - (1 - P.val.2 + α') = -2 + P.val.2 - α' by ring] using hbnd

end Riesz1
