/-
Copyright (c) 2026 Jeanne Boursier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeanne Boursier
-/
module

public import Riesz1.Variance.RegMicroKernelRepresentation
public import Riesz1.Kernel.AdmissibilityRegularityAbsoluteContinuity
public import Riesz1.ToMathlib.MollifierPointwise.Circle

/-!
# The inverse representation from profile regularity

This connects the inverse-transport identity to the actual (A1)–(A3)
predicates, supplying its differentiability and integrability certificates.
The inverse representative has the same mollification as the profile for every
radius and every evaluation point. These are the representative-identification
clauses of Lemma 5.3. No pointwise derivative estimate
for the profile is asserted here.
-/

public section

open MeasureTheory Set Filter
open scoped Topology

namespace Riesz1

/-- The predicates (A1)–(A3) imply the inverse representation, with no auxiliary
regularity assumptions on the transport. The smoothing equality holds pointwise
because convolution is insensitive to the a.e. choice of representative. -/
theorem regMicroKernel_profile_representation (P : Parameters) (L : Length)
    (η B : ℝ) (hη : 0 < η) (hB : 0 ≤ B)
    (f : {f : Circle L → ℝ // MemLp (fun x => (f x : ℂ)) 2 (arclength L)})
    (n : ℕ+) (marks : Fin (n : ℕ) → ℝ) (α C : ℝ)
    (hα0 : P.val.2 - 1 ≤ α) (hα1 : α < P.val.2 / 2) (hC : 0 ≤ C)
    (hprim : PrimitiveRegularity L η P.val.2 B f)
    (hreg : TransportRegularity P L f n marks α C) :
    ∃ ψ : {g : Circle L → ℝ // MemLp (fun x => (g x : ℂ)) 2 (arclength L)},
      Continuous ψ.val ∧
      (∀ k : ℤ, coeff L
        ⟨(fun x => (ψ.val x : ℂ)), complexL2Integrable L _ ψ.property⟩ k =
          transportCoeffs P L f k) ∧
      LocallyIntegrable (deriv (fun t : ℝ => ψ.val (t : Circle L))) volume ∧
      (∀ u v : ℝ, AbsolutelyContinuousOnInterval
        (fun t : ℝ => ψ.val (t : Circle L)) u v) ∧
      (∀ x : ℝ, (∀ j, (x : Circle L) ≠ (marks j : Circle L)) →
        ContDiffAt ℝ 2 (fun t : ℝ => ψ.val (t : Circle L)) x) ∧
      (∀ᵐ x : ℝ ∂(volume.restrict (Ioc (-(L.val / 2)) (L.val / 2))),
        f.val (x : Circle L) =
          (∫ y in Ioc (-(L.val / 2)) (L.val / 2), f.val (y : Circle L)) / L.val +
            inverseConv P L.val (deriv (fun t : ℝ => ψ.val (t : Circle L))) x) ∧
      ∀ (ρ : ℝ → ℝ) (h x : ℝ),
        circleMollify ρ L.val h (fun t : ℝ => f.val (t : Circle L)) x =
          circleMollify ρ L.val h
            (fun t =>
              (∫ y in Ioc (-(L.val / 2)) (L.val / 2), f.val (y : Circle L)) / L.val +
                inverseConv P L.val (deriv (fun u : ℝ => ψ.val (u : Circle L))) t) x := by
  have : Fact (0 < L.val) := ⟨L.property⟩
  obtain ⟨ψ, hc, hψ, hcoef, hpoint⟩ :=
    exists_continuous_transport_with_regularity P L η B hη hB f n marks α C hprim hreg
  have hi := Internal.locallyIntegrable_deriv_of_transport_bound P L marks α C
    hα0 hα1 hC _ hpoint
  have hdiff : ∀ x : ℝ, x ∉ {t : ℝ | ∃ j, (t : Circle L) = (marks j : Circle L)} →
      DifferentiableAt ℝ (fun t : ℝ => ψ (t : Circle L)) x := by
    intro x hx
    exact (hpoint x (by simpa only [mem_ofPred_eq, not_exists] using hx)).1.differentiableAt
      (by norm_num)
  have hcount := CircleSingularity.countable_marked_lifts (T := L.val) marks
  have hAC := PuncturedDerivative.absolutelyContinuousOnInterval_of_countable_exceptional
    (hc.comp (AddCircle.continuous_mk' L.val)) hcount hdiff hi
  have hψi : IntervalIntegrable (deriv (fun t : ℝ => ψ (t : Circle L))) volume 0 L.val :=
    IntegrableOn.intervalIntegrable (hi.integrableOn_isCompact isCompact_uIcc)
  have hrep := inverse_representation P L f ⟨ψ, hψ⟩ hc hcount hdiff hψi hcoef
  refine ⟨⟨ψ, hψ⟩, hc, hcoef, hi, hAC, fun x hx => (hpoint x hx).1, hrep, ?_⟩
  intro ρ h x
  unfold circleMollify
  rw [intervalIntegral.integral_of_le (by linarith [L.property]),
    intervalIntegral.integral_of_le (by linarith [L.property])]
  apply integral_congr_ae
  filter_upwards [hrep] with t ht
  rw [ht]

end Riesz1
